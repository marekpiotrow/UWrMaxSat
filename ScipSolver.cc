/**************************************************************************************[MsSolver.cc]
  Copyright (c) 2021-2024, Marek Piotrów

  Based on an extension of UWrMaxSat done by Dongxu Wang (2021) that added SCIP solver to the project.

  Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
  associated documentation files (the "Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge, publish, distribute,
  sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all copies or
  substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
  NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
  DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
  OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
  **************************************************************************************************/

#ifdef USE_SCIP

#include "MsSolver.h"
#include <vector>
#include <future>
#include <atomic>
#include <chrono>
#include <thread>
#include <scip/struct_message.h>

#define MY_SCIP_CALL(x) do{ SCIP_RETCODE _r_; \
    if ((_r_ = (x)) != SCIP_OKAY) { reportf("SCIP error <%d>\n",_r_); return l_Undef; }} while(0)

std::atomic<char> opt_finder(OPT_NONE);

void scip_interrupt_solve(ScipSolver &scip_solver)
{
    if (scip_solver.scip != nullptr) {
        if (opt_verbosity > 0)
            reportf("SCIP solver is interrupted (UWrMaxSat found OPT).\n");
        SCIPinterruptSolve(scip_solver.scip);
        SCIPinterruptLP(scip_solver.scip, TRUE);
    }
    scip_solver.interrupted = true;
    if (scip_solver.asynch_result.valid()) scip_solver.asynch_result.get();
}

lbool set_scip_var(SCIP *scip, MsSolver *solver, std::vector<SCIP_VAR *> &vars, Lit lit)
{
    SCIP_VAR *scip_var = vars[var(lit)];
    if (scip_var == nullptr) {
        Var v = var(lit);
        std::string name = "x" + std::to_string(v + 1);
        SCIP_Real lb = 0, ub = 1;
        if (solver->value(v) == l_False) ub = 0;
        else if (solver->value(v) == l_True) lb = 1;
        if (solver->ipamir_used && solver->global_assump_vars.at(v)) {
            if (Sort::bin_search(solver->global_assumptions,lit) >= 0) {
                if (sign(lit)) ub = 0; else lb = 1;
            } else if (sign(lit)) lb = 1; else ub = 0;
        }
        if (lb > ub) return l_False;
        MY_SCIP_CALL(SCIPcreateVarBasic(scip, &scip_var, name.c_str(), lb, ub, 0, SCIP_VARTYPE_BINARY));
        MY_SCIP_CALL(SCIPaddVar(scip, scip_var));
        vars[var(lit)] = scip_var;
    }
    return l_Undef;
}

template<class T>
lbool add_constr(SCIP *scip,
                        MsSolver *solver,
                        const T &ps,
                        std::vector<SCIP_VAR *> &vars,
                        const std::string &const_name)
{
    SCIP_CONS *cons = nullptr;
    MY_SCIP_CALL(SCIPcreateConsBasicPseudoboolean(scip, &cons, const_name.c_str(), nullptr, 0, nullptr, nullptr, 0, nullptr, nullptr, nullptr, 1.0, FALSE, nullptr, -SCIPinfinity(scip), SCIPinfinity(scip)));
    int lhs = 1;
    for (int j = 0; j < ps.size(); j++)
    {
        auto lit = ps[j];
        if (solver->value(lit) == l_False) continue;
        if (set_scip_var(scip, solver, vars, lit)== l_False) return l_False;
        auto v = vars[var(lit)];
        MY_SCIP_CALL(SCIPaddCoefPseudoboolean(scip, cons, v, sign(lit) ? -1 : 1));
        if (sign(lit)) lhs--;
    }
    MY_SCIP_CALL(SCIPchgLhsPseudoboolean(scip, cons, lhs));
    MY_SCIP_CALL(SCIPaddCons(scip, cons));
    MY_SCIP_CALL(SCIPreleaseCons(scip, &cons));
    return l_Undef;
}

lbool add_pb_constrs(ScipSolver &scip_solver, MsSolver *solver)
{
  SCIP *scip = scip_solver.scip;
  for (int i = 0; i < solver->constrs.size(); i++) {
    if (solver->constrs[i] == NULL) continue;
    Linear &c = *solver->constrs[i]; assert(c.lo != Int_MIN || c.hi != Int_MAX);
    std::string const_name = "pbc" + std::to_string(i);
    SCIP_Real lhs = (c.lo == Int_MIN ? -SCIPinfinity(scip) : tolong(c.lo)), 
              rhs = (c.hi == Int_MAX ?  SCIPinfinity(scip) : tolong(c.hi));
    SCIP_CONS *cons = nullptr;
    MY_SCIP_CALL(SCIPcreateConsBasicPseudoboolean(scip, &cons, const_name.c_str(), nullptr, 0, nullptr, nullptr, 0, nullptr, nullptr, nullptr, 1.0, FALSE, nullptr, -SCIPinfinity(scip), SCIPinfinity(scip)));
    for (int j = 0; j < c.size; j++)
    {
        Lit lit = c[j];
        if (solver->value(lit) == l_False) continue;
        if (set_scip_var(scip, solver, scip_solver.vars, lit)== l_False) return l_False;
        auto v = scip_solver.vars[var(lit)];
        SCIP_Real coeff = tolong(c(j));
        MY_SCIP_CALL(SCIPaddCoefPseudoboolean(scip, cons, v, sign(lit) ? -coeff : coeff));
        if (sign(lit)) lhs -= coeff, rhs -= coeff;
    }
    MY_SCIP_CALL(SCIPchgLhsPseudoboolean(scip, cons, lhs));
    MY_SCIP_CALL(SCIPchgRhsPseudoboolean(scip, cons, rhs));
    MY_SCIP_CALL(SCIPaddCons(scip, cons));
    MY_SCIP_CALL(SCIPreleaseCons(scip, &cons));
  }
  return l_Undef;
}

void uwrLogMessage(FILE *file, const char *msg)
{
    if (msg != nullptr) fputs("c SCIP: ", file), fputs(msg, file);
    fflush(file);
}
SCIP_DECL_MESSAGEINFO(uwrMessageInfo) { (void)(messagehdlr); uwrLogMessage(file, msg); }

lbool printScipStats(ScipSolver *scip_solver)
{
    std::lock_guard<std::mutex> lck(stdout_mtx);
    SCIP_MESSAGEHDLR *mh = SCIPgetMessagehdlr(scip_solver->scip);
    auto mi = mh->messageinfo;
    mh->messageinfo = uwrMessageInfo;
    MY_SCIP_CALL(SCIPsetMessagehdlr(scip_solver->scip, mh));
    printf("c _______________________________________________________________________________\nc \n");
    SCIPprintStatusStatistics(scip_solver->scip, nullptr);
    SCIPprintOrigProblemStatistics(scip_solver->scip, nullptr);
    SCIPprintTimingStatistics(scip_solver->scip, nullptr);
    mh->messageinfo = mi;
    MY_SCIP_CALL(SCIPsetMessagehdlr(scip_solver->scip, mh));
    return l_Undef;
}

void saveFixedVariables(ScipSolver *scip_solver)
{
    std::lock_guard<std::mutex> lck(fixed_vars_mtx);
    int fixed = 0;
    for (int i = 0; i < (int)scip_solver->vars.size(); i++) {
        SCIP_VAR *v = scip_solver->vars[i];
        if (v != nullptr) {
            SCIP_VAR * trans_var = SCIPvarGetTransVar(v);
            if (trans_var != nullptr && SCIPvarGetStatus(trans_var) == SCIP_VARSTATUS_FIXED) {
                SCIP_Real lb = SCIPvarGetLbGlobal(trans_var),
                          ub = SCIPvarGetUbGlobal(trans_var);
                lbool    val = (SCIPisZero(scip_solver->scip, lb) &&
                        SCIPisZero(scip_solver->scip, ub)     ? l_False :
                        (SCIPisZero(scip_solver->scip, lb - 1) && 
                         SCIPisZero(scip_solver->scip, ub - 1) ? l_True : l_Undef));
                if (val != l_Undef) 
                    scip_solver->fixed_vars.push(mkLit(i, val == l_False)), ++fixed;
            }
        }
    }
    if (opt_verbosity >= 2 && fixed > 0) reportf("SCIP fixed %d vars\n", fixed);
}

lbool scip_solve_async(ScipSolver *scip_solver, MsSolver *solver)
{
    extern double opt_scip_cpu, opt_scip_cpu_add;
    lbool found_opt = l_Undef;
    SCIP_STATUS status;
    int64_t best_value = INT64_MAX;
    int try_count = 3;
    bool try_again, obj_limit_applied = false;
    int64_t bound_gap = INT64_MAX;

    {
        std::lock_guard<std::mutex> lck(optsol_mtx);
        if (solver->best_goalvalue < WEIGHT_MAX) {
            MY_SCIP_CALL(SCIPsetObjlimit(scip_solver->scip, 
              SCIP_Real(tolong(solver->best_goalvalue * solver->goal_gcd - scip_solver->obj_offset))));
            obj_limit_applied = true;
        }
        if (solver->LB_goalvalue > 0) {
            MY_SCIP_CALL(SCIPupdateLocalDualbound(scip_solver->scip, SCIP_Real(tolong(solver->LB_goalvalue * solver->goal_gcd - scip_solver->obj_offset))));
            if (obj_limit_applied) bound_gap = tolong(solver->best_goalvalue - solver->LB_goalvalue);
        }
    }
    MY_SCIP_CALL(SCIPsetObjIntegral(scip_solver->scip));
    do {
       try_again = false; 
       MY_SCIP_CALL(SCIPsolve(scip_solver->scip));
       status = SCIPgetStatus(scip_solver->scip);
    if (status == SCIP_STATUS_OPTIMAL)
    {
        found_opt = l_True;
        SCIP_SOL *sol = SCIPgetBestSol(scip_solver->scip);
        assert(sol != nullptr);
        // MY_SCIP_CALL(SCIPprintSol(scip_solver->scip, sol, nullptr, FALSE));
        SCIP_Bool feasible = FALSE;
        MY_SCIP_CALL(SCIPcheckSolOrig(scip_solver->scip, sol, &feasible, FALSE, FALSE));
        if (!feasible) { found_opt = l_Undef; goto clean_and_return; }

        best_value = scip_solver->obj_offset + long(round(SCIPgetSolOrigObj(scip_solver->scip, sol)));
        for (Var x = 0; x < (int)scip_solver->vars.size(); x++)
        {
            if (scip_solver->vars[x] != nullptr) {
                SCIP_Real v = SCIPgetSolVal(scip_solver->scip, sol, scip_solver->vars[x]);
                scip_solver->model[x] = lbool(v > 0.5);
            }
        }
    } else if (status == SCIP_STATUS_INFEASIBLE) {
        if (obj_limit_applied) { // SCIP proved optimality of the last MaxSAT o-value 
            if (!solver->ipamir_used || opt_verbosity > 0) {
                reportf("SCIP proved optimality of the last o-value\n");
                solver->printStats(true);
            }
            found_opt = l_True;
            goto clean_and_return;
        } else {
            std::lock_guard<std::mutex> lck(optsol_mtx);
            found_opt = l_False;
            char test = OPT_NONE;
            if (!solver->ipamir_used && opt_finder.compare_exchange_strong(test, OPT_SCIP) ) { 
                if (opt_verbosity > 0) {
                    reportf("SCIP result: UNSATISFIABLE\n");
                    printScipStats(scip_solver);
                    solver->printStats(false);
                }
                printf("s UNSATISFIABLE\n"); fflush(stdout);
                std::_Exit(20);
            }
        }
    } else {
        SCIP_Real dualb = SCIPgetDualbound(scip_solver->scip), primb = SCIPgetPrimalbound(scip_solver->scip);
        int64_t lbound = (!SCIPisInfinity(scip_solver->scip, dualb) ? 
                int64_t(round(dualb)) + scip_solver->obj_offset : INT64_MIN);
        int64_t ubound = (!SCIPisInfinity(scip_solver->scip, primb) ? 
                int64_t(round(primb)) + scip_solver->obj_offset : INT64_MAX);
        if (opt_finder.load() != OPT_MSAT && opt_scip_cpu > 0 && (!solver->ipamir_used || opt_verbosity > 0))
            reportf("SCIP timeout with lower and upper bounds: [%lld, %lld]\n", lbound, ubound);
        int64_t gcd = fromweight(solver->goal_gcd);
        if (!SCIPisInfinity(scip_solver->scip, dualb)) {
            std::lock_guard<std::mutex> lck(optsol_mtx);
            int64_t lb = (gcd == 1 ? lbound : (lbound > 0 ? lbound + gcd - 1 : lbound) / gcd);
            if (Int(lb) > solver->scip_LB) solver->scip_LB = lb, solver->scip_foundLB = true;
            if (Int(lb) == solver->best_goalvalue) {
                if (!solver->ipamir_used || opt_verbosity > 0) {
                    reportf("SCIP proved optimality of the last o-value\n");
                    solver->printStats(true);
                }
                found_opt = l_True;
                goto clean_and_return;
            }
        }
        if (!SCIPisInfinity(scip_solver->scip, primb)) {
            int64_t ub = (gcd == 1 ? ubound : (ubound < 0 ? ubound - gcd + 1 : ubound) / gcd);
            if (Int(ub) < solver->scip_UB) solver->scip_UB = ub, solver->scip_foundUB = true;
            SCIP_SOL *sol = SCIPgetBestSol(scip_solver->scip);
            if (sol != nullptr) {
                Int scip_sol = (scip_solver->obj_offset + int64_t(round(SCIPgetSolOrigObj(scip_solver->scip, sol))))/gcd;
                SCIP_Bool feasible = FALSE;
                MY_SCIP_CALL(SCIPcheckSolOrig(scip_solver->scip, sol, &feasible, FALSE, FALSE));
                if (feasible && scip_sol < solver->best_goalvalue) {
                    for (Var x = 0; x < (int)scip_solver->vars.size(); x++)
                        if (scip_solver->vars[x] != nullptr) {
                            SCIP_Real v = SCIPgetSolVal(scip_solver->scip, sol, scip_solver->vars[x]);
                            scip_solver->model[x] = lbool(v > 0.5);
                        }
                    std::lock_guard<std::mutex> lck(optsol_mtx);
                    if (opt_finder.load() != OPT_MSAT) {
                        extern bool opt_satisfiable_out;
                        vec<lbool> opt_model(scip_solver->model.size()); 
                        for (int i = scip_solver->model.size() - 1; i >= 0 ; i--) opt_model[i] = scip_solver->model[i];
                        solver->sat_solver.extendGivenModel(opt_model);
                        solver->best_model.clear();
                        for (int x = 0; x < solver->pb_n_vars; x++) solver->best_model.push(opt_model[x] != l_False);
                        Minisat::vec<Lit> soft_unsat; // Not used in this context
                        solver->best_goalvalue = solver->fixed_goalval + evalGoal(solver->soft_cls, solver->best_model, soft_unsat);
                        char *tmp = toString(solver->best_goalvalue * solver->goal_gcd);
                        if (opt_satisfiable_out && opt_output_top < 0 && (opt_satlive || opt_verbosity == 0))
                            printf("o %s\n", tmp), fflush(stdout);
                        else if (opt_verbosity > 0 || !opt_satisfiable_out && !solver->ipamir_used) 
                            reportf("%s solution: %s\n", (found_opt == l_True ? "Next" : "Found"), tmp);
                        xfree(tmp);
                        solver->satisfied = true;
                    }
                }
            }
            if (!scip_solver->interrupted && opt_scip_cpu > 0 && lbound != INT64_MIN && try_count > 0 && 
                  double(ubound - lbound)/max(int64_t(1),max(abs(lbound),abs(ubound))) < 0.10 &&
                  ubound - lbound < bound_gap) {
                try_count--; opt_scip_cpu += opt_scip_cpu_add;
                bound_gap = ubound - lbound;
                MY_SCIP_CALL(SCIPsetRealParam(scip_solver->scip, "limits/time", opt_scip_cpu));
                //MY_SCIP_CALL(SCIPrestartSolve(scip_solver->scip));
                if (!solver->ipamir_used || opt_verbosity > 0) 
                    reportf("Restarting SCIP solver (with time-limit: %.0fs) ...\n", opt_scip_cpu);
                try_again = true;
            }
        }
        if (opt_scip_cpu == 0 && !scip_solver->interrupted) {
            saveFixedVariables(scip_solver);
            MY_SCIP_CALL(SCIPsetRealParam(scip_solver->scip, "limits/time", 1e+20));
            try_again = true;
        }
    }
    } while (try_again);

    // if optimum found, exit
    if (found_opt == l_True) {
        std::lock_guard<std::mutex> lck(optsol_mtx);
	char test = OPT_NONE;
        if (opt_finder.compare_exchange_strong(test, OPT_SCIP)) {
	    if (!scip_solver->pb_decision_problem && (!solver->ipamir_used || opt_verbosity > 0)) 
		    reportf("SCIP optimum (rounded): %" PRId64 "\n", best_value);
	    solver->best_goalvalue = best_value;
            vec<lbool> opt_model(scip_solver->model.size()); 
            for (int i = scip_solver->model.size() - 1; i >= 0 ; i--)
                opt_model[i] = (scip_solver->model[i] == l_Undef && !solver->sat_solver.isEliminated(i) ? l_False : scip_solver->model[i]);
            solver->sat_solver.extendGivenModel(opt_model);
            solver->best_model.clear();
            for (int x = 0; x < solver->pb_n_vars; x++) solver->best_model.push(opt_model[x] != l_False);
            Minisat::vec<Lit> soft_unsat; // Not used in this context
            solver->best_goalvalue = (solver->fixed_goalval + evalGoal(solver->soft_cls, solver->best_model, soft_unsat)) * solver->goal_gcd;

	    extern bool opt_satisfiable_out;
	    opt_satisfiable_out = scip_solver->pb_decision_problem;

            if (opt_verbosity >= 1) {
                printScipStats(scip_solver);
                solver->printStats(false);
            }
            if (!solver->ipamir_used) {
                outputResult(*solver, !scip_solver->pb_decision_problem);
		std::this_thread::sleep_for(std::chrono::milliseconds(10));
                //MY_SCIP_CALL(SCIPfree(&scip_solver->scip));
                std::_Exit(30);
            }
        }
    } else saveFixedVariables(scip_solver);
clean_and_return:
    // release SCIP vars
    for (auto v: scip_solver->vars)
        if (v != nullptr) MY_SCIP_CALL(SCIPreleaseVar(scip_solver->scip, &v));
    scip_solver->vars.clear();
    scip_solver->interrupted = false;
    extern bool opt_scip_parallel;

    MY_SCIP_CALL(SCIPfree(&scip_solver->scip));
    scip_solver->scip = nullptr;
    if ((opt_scip_parallel || solver->ipamir_used) && found_opt != l_Undef)
        solver->sat_solver.interrupt();
    return found_opt;
}

#ifdef CADICAL
class ScipClauseIterator : public CaDiCaL::ClauseIterator {
    SCIP *scip;
    MsSolver *solver;
    std::vector<SCIP_VAR *> &vars;
    int count;
public:
    ScipClauseIterator(SCIP *s, MsSolver *ms, std::vector<SCIP_VAR *> &v) : scip(s), 
        solver(ms), vars(v), count(0) {}
    bool clause(const std::vector<int> &c) {
        Minisat::vec<Lit> ps;
        std::string cons_name = "cons" + std::to_string(count++);
        for (int l : c) ps.push(mkLit(std::abs(l)-1, l < 0));
        add_constr(scip, solver, ps, vars, cons_name);
        return true;
    }
};
#endif

lbool MsSolver::scip_init(ScipSolver &scip_solver, int sat_orig_vars)
{
    extern double opt_scip_cpu, opt_scip_cpu_add;
    extern bool opt_force_scip;

    if (scip_solver.scip != nullptr) return l_Undef;

    bool res = sat_solver.reduceProblem();
    int sat_orig_cls = sat_solver.nClauses();

    if (!res || !opt_force_scip &&
            (sat_solver.nFreeVars() >= 100000 || sat_orig_cls >= 600000 || soft_cls.size() >= 100000))
        return l_Undef;

    if (!ipamir_used || opt_verbosity >= 2)
        reportf("Using SCIP solver, version %.2f.%d, https://www.scipopt.org\n", 
            SCIPversion(), SCIPtechVersion());

    // 1. create scip context object
    SCIP *scip = nullptr;
    MY_SCIP_CALL(SCIPcreate(&scip));
    MY_SCIP_CALL(SCIPincludeDefaultPlugins(scip));
    char *base = nullptr;
    if (opt_input != nullptr) base = strrchr(opt_input,'/'), base = (base ? base+1 : opt_input); 
    MY_SCIP_CALL(SCIPcreateProbBasic(scip, (base != nullptr ? base : "IPAMIR of UWrMaxSat")));
    MY_SCIP_CALL(SCIPsetEmphasis(scip, SCIP_PARAMEMPHASIS_DEFAULT, TRUE));
    if (opt_scip_cpu > 0) 
        MY_SCIP_CALL(SCIPsetRealParam(scip, "limits/time", opt_scip_cpu));
    else
        MY_SCIP_CALL(SCIPsetRealParam(scip, "limits/time", opt_scip_cpu_add));
    if (opt_verbosity <= 1)
        MY_SCIP_CALL(SCIPsetIntParam(scip, "display/verblevel", 0));
    if (declared_intsize > 0 && declared_intsize < 49) {
        SCIP_Real feastol, newfeastol = pow(0.5,declared_intsize), epsilon, sumepsilon;
        MY_SCIP_CALL(SCIPgetRealParam(scip, "numerics/feastol", &feastol));
        MY_SCIP_CALL(SCIPgetRealParam(scip, "numerics/epsilon", &epsilon));
        MY_SCIP_CALL(SCIPgetRealParam(scip, "numerics/sumepsilon", &sumepsilon));
        if (newfeastol < feastol)
            MY_SCIP_CALL(SCIPsetRealParam(scip, "numerics/feastol", newfeastol));
        if (newfeastol < epsilon)
            MY_SCIP_CALL(SCIPsetRealParam(scip, "numerics/epsilon", newfeastol));
        if (newfeastol < sumepsilon)
            MY_SCIP_CALL(SCIPsetRealParam(scip, "numerics/sumepsilon", newfeastol));
    }
    scip_solver.model.resize(sat_orig_vars);
    for (Var x = sat_orig_vars - 1; x >= 0; x--) scip_solver.model[x] = sat_solver.value(x);

    // 2. create variable
    scip_solver.vars.resize(sat_orig_vars, nullptr);
    if (ipamir_used)
        for (int i = 0; i < global_assumptions.size(); i++)
            if (set_scip_var(scip, this, scip_solver.vars, global_assumptions[i]) == l_False)
                return l_False;

    // 3. add constraint
    scip_solver.scip = scip;
  if (opt_maxsat) {
#ifdef CADICAL
    ScipClauseIterator it(scip, this, scip_solver.vars);
    sat_solver.solver->traverse_clauses(it);
#else
    for (int i = 0; i < sat_orig_cls; i++)
    {
        bool is_satisfied;
        const Minisat::Clause &ps = sat_solver.getClause(i, is_satisfied);
        if (!is_satisfied)
        {
            std::string cons_name = "cons" + std::to_string(i);
            add_constr(scip, this, ps, scip_solver.vars, cons_name);
        }
    }
#endif
  } else add_pb_constrs(scip_solver, this);

    return l_Undef;
}

lbool MsSolver::scip_solve(const Minisat::vec<Lit> *assump_ps,
                                  const vec<Int> *assump_Cs,
                                  const IntLitQueue *delayed_assump,
                                  bool weighted_instance,
                                  int sat_orig_vars,
                                  int sat_orig_cls,
                                  ScipSolver &scip_solver)
{
    extern double opt_scip_cpu, opt_scip_delay;
    extern bool opt_scip_parallel;

    if (scip_solver.started) return l_Undef;
    scip_solver.started = true;

    if (scip_solver.scip == nullptr) {
        scip_init(scip_solver, sat_orig_vars);
        if (scip_solver.scip == nullptr) return l_Undef;
    }
    if (size_t(sat_orig_vars) > scip_solver.vars.size()) scip_solver.vars.resize(sat_orig_vars, nullptr);
    if (size_t(sat_orig_vars) > scip_solver.model.size()) scip_solver.model.resize(sat_orig_vars);

    int64_t obj_offset = 0;
    int obj_vars = 0;
    auto set_var_coef = [&scip_solver, &obj_offset, &obj_vars, this](Lit relax, weight_t weight)
    {
        if (value(relax) != l_Undef) {
            if (value(relax) == l_False) obj_offset += fromweight(weight) * fromweight(this->goal_gcd);
        } else {
            obj_vars++;
            weight_t coef = sign(relax) ? weight : -weight;
            coef *= this->goal_gcd;
            if (set_scip_var(scip_solver.scip, this, scip_solver.vars, relax) == l_False)
                return l_False;
            auto v = scip_solver.vars[var(relax)];
            MY_SCIP_CALL(SCIPaddVarObj(scip_solver.scip, v, double(coef)));
            if (! sign(relax))
                obj_offset -= fromweight(coef);
        }
        return l_Undef;
    };
    if (weighted_instance || !opt_maxsat)
    {
        int last = (!opt_maxsat ? soft_cls.size() : top_for_strat);
        for (int i = 0; i < last; ++i)
        {
            const Pair<weight_t, Minisat::vec<Lit> *> &weight_ps = soft_cls[i];
            const Minisat::vec<Lit> &ps = *(weight_ps.snd);
            auto relax = ps.last();
            if (ps.size() > 1) relax = ~relax;
            weight_t weight = weight_ps.fst;
            if (set_var_coef(relax, weight) == l_False) return l_False;
            if (ps.size() > 1)
            {
                std::string cons_name = "soft_cons" + std::to_string(i);
                add_constr(scip_solver.scip, this, ps, scip_solver.vars, cons_name);
            }
        }
    }

    // 4. set objective
    if (opt_verbosity >= 2)
        reportf("SCIPobj: soft_cls.size=%u, assump_ps->size=%u, delayed_assump.size=%u, goal_gcd=%ld, hard_cls=%d\n", 
            top_for_strat, assump_ps->size(), delayed_assump->getHeap().size() - 1, fromweight(goal_gcd),
            sat_orig_cls);
    if (opt_maxsat) {
        for (int i = 0; i < assump_ps->size(); ++i)
            if (set_var_coef((*assump_ps)[i], tolong((*assump_Cs)[i])) == l_False) return l_False;
        for (int i = 1; i < delayed_assump->getHeap().size(); ++i)
        {
            const Pair<Int, Lit> &weight_lit = delayed_assump->getHeap()[i];
            Lit relax = weight_lit.snd;
            weight_t weight = tolong(weight_lit.fst);
            if (set_var_coef(relax, weight) == l_False) return l_False;
        }
    }
    if (opt_verbosity >= 2)
        reportf("SCIPobj: obj_var=%d, obj_offset=%" PRId64 ", ob_offset_to_add: %ld %ld\n", obj_vars, obj_offset,
                fromweight(goal_gcd) * tolong(fixed_goalval), fromweight(goal_gcd) * tolong(harden_goalval));
    if (opt_maxsat)
        obj_offset += fromweight(goal_gcd) * tolong(fixed_goalval + harden_goalval);
    else
        obj_offset += fromweight(goal_gcd) * tolong(fixed_goalval);

    // 5. do solve
    // MY_SCIP_CALL((SCIPwriteOrigProblem(scip, "1.lp", nullptr, FALSE)));
    // MY_SCIP_CALL((SCIPwriteTransProblem(scip, "2.lp", nullptr, FALSE)));
    if (!ipamir_used || opt_verbosity > 0) reportf("Starting SCIP solver %s (with time-limit: %.0fs) ...\n", 
            (opt_scip_parallel? "in a separate thread" : ""), opt_scip_cpu);

    scip_solver.obj_offset = obj_offset;
    if (opt_scip_delay > cpuTime() + 10) {
        scip_solver.must_be_started = true;
        if (!ipamir_used || opt_verbosity > 0) reportf("SCIP start delayed for at least %.0fs\n", opt_scip_delay - cpuTime());  
        return l_Undef;
    } else if (opt_scip_parallel) {
        scip_solver.asynch_result = std::async(std::launch::async, scip_solve_async, &scip_solver, this);
        return l_Undef;
    } else 
        return scip_solve_async(&scip_solver, this);
}

#endif
