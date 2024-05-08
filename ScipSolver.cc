/**************************************************************************************[MsSolver.cc]
  Copyright (c) 2021, Marek Piotrów

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
    MY_SCIP_CALL(SCIPcreateConsBasicLinear(scip, &cons, const_name.c_str(), 0, nullptr, nullptr, 0, SCIPinfinity(scip)));
    int lhs = 1;
    for (int j = 0; j < ps.size(); j++)
    {
        auto lit = ps[j];
        if (solver->value(lit) == l_False) continue;
        if (set_scip_var(scip, solver, vars, lit)== l_False) return l_False;
        auto v = vars[var(lit)];
        MY_SCIP_CALL(SCIPaddCoefLinear(scip, cons, v, sign(lit) ? -1 : 1));
        if (sign(lit)) lhs--;
    }
    MY_SCIP_CALL(SCIPchgLhsLinear(scip, cons, lhs));
    MY_SCIP_CALL(SCIPaddCons(scip, cons));
    MY_SCIP_CALL(SCIPreleaseCons(scip, &cons));
    return l_Undef;
}

void uwrLogMessage(FILE *file, const char *msg)
{
    if (msg != nullptr) fputs("c SCIP: ", file), fputs(msg, file);
    fflush(file);
}
SCIP_DECL_MESSAGEINFO(uwrMessageInfo) { (void)(messagehdlr); uwrLogMessage(file, msg); }

lbool scip_solve_async(SCIP *scip, std::vector<SCIP_VAR *> vars, std::vector<lbool> scip_model, MsSolver *solver, int64_t obj_offset)
{
    extern double opt_scip_cpu, opt_scip_cpu_add;
    lbool found_opt = l_Undef;
    SCIP_STATUS status;
    int64_t best_value = INT64_MAX;
    int try_count = 3;
    bool try_again, obj_limit_applied = false;
    int64_t bound_gap = INT64_MAX;

    if (solver->best_goalvalue < WEIGHT_MAX) {
        MY_SCIP_CALL(SCIPsetObjlimit(scip, 
                          SCIP_Real(tolong(solver->best_goalvalue * solver->goal_gcd - obj_offset))));
        obj_limit_applied = true;
    }
    MY_SCIP_CALL(SCIPsetObjIntegral(scip));
    do {
       try_again = false; 
       MY_SCIP_CALL(SCIPsolve(scip));
       status = SCIPgetStatus(scip);
    if (status == SCIP_STATUS_OPTIMAL)
    {
        found_opt = l_True;
        SCIP_SOL *sol = SCIPgetBestSol(scip);
        assert(sol != nullptr);
        // MY_SCIP_CALL(SCIPprintSol(scip, sol, nullptr, FALSE));
        best_value = obj_offset + long(round(SCIPgetSolOrigObj(scip, sol)));
        for (Var x = 0; x < (int)vars.size(); x++)
        {
            if (vars[x] != nullptr) {
                SCIP_Real v = SCIPgetSolVal(scip, sol, vars[x]);
                scip_model[x] = lbool(v > 0.5);
            }
        }
    } else if (status == SCIP_STATUS_INFEASIBLE) {
        if (obj_limit_applied) { // SCIP proved optimality of the last MaxSAT o-value 
            if (!solver->ipamir_used || opt_verbosity > 0)
                reportf("SCIP proved optimality of the last o-value\n");
            solver->printStats(true);
            return l_True;
        } else {
            found_opt = l_False;
            if (opt_verbosity > 0) reportf("SCIP result: UNSATISFIABLE\n");
            if (!solver->ipamir_used) { 
                printf("s UNSATISFIABLE\n");
                std::_Exit(20);
            }
        }
    } else {
        SCIP_Real dualb = SCIPgetDualbound(scip), primb = SCIPgetPrimalbound(scip);
        int64_t lbound = (!SCIPisInfinity(scip, dualb) ? int64_t(round(dualb)) + obj_offset : INT64_MIN);
        int64_t ubound = (!SCIPisInfinity(scip, primb) ? int64_t(round(primb)) + obj_offset : INT64_MAX);
        if (!solver->ipamir_used || opt_verbosity > 0)
            reportf("SCIP timeout with lower and upper bounds: [%lld, %lld]\n", lbound, ubound);
        int64_t gcd = fromweight(solver->goal_gcd);
        if (!SCIPisInfinity(scip, dualb)) {
            int64_t lb = (gcd == 1 ? lbound : (lbound > 0 ? lbound + gcd - 1 : lbound) / gcd);
            if (Int(lb) > solver->scip_LB) solver->scip_LB = lb, solver->scip_foundLB = true;
        }
        if (!SCIPisInfinity(scip, primb)) {
            int64_t ub = (gcd == 1 ? ubound : (ubound < 0 ? ubound - gcd + 1 : ubound) / gcd);
            if (Int(ub) < solver->scip_UB) solver->scip_UB = ub, solver->scip_foundUB = true;
            SCIP_SOL *sol = SCIPgetBestSol(scip);
            if (sol != nullptr) {
                Int scip_sol = (obj_offset + int64_t(round(SCIPgetSolOrigObj(scip, sol)))) / gcd;
                if (scip_sol < solver->best_goalvalue) {
                    for (Var x = 0; x < (int)vars.size(); x++)
                        if (vars[x] != nullptr) {
                            SCIP_Real v = SCIPgetSolVal(scip, sol, vars[x]);
                            scip_model[x] = lbool(v > 0.5);
                        }
                    std::lock_guard<std::mutex> lck(optsol_mtx);
                    if (opt_finder.load() != OPT_MSAT) {
                        vec<lbool> opt_model(scip_model.size()); 
                        for (int i = scip_model.size() - 1; i >= 0 ; i--) opt_model[i] = scip_model[i];
                        solver->sat_solver.extendGivenModel(opt_model);
                        solver->best_model.clear();
                        for (int x = 0; x < solver->pb_n_vars; x++) solver->best_model.push(opt_model[x] != l_False);
                        Minisat::vec<Lit> soft_unsat; // Not used in this context
                        solver->best_goalvalue = (solver->fixed_goalval + evalGoal(solver->soft_cls, solver->best_model, soft_unsat)) * solver->goal_gcd;
                        char *p;
                        printf("o %s\n", p=toString(solver->best_goalvalue)); xfree(p);
                        solver->satisfied = true;
                    }
                }
            }
            if (lbound != INT64_MIN &&  try_count > 0 && double(ubound - lbound)/ubound < 0.10 && ubound - lbound < bound_gap) {
                try_count--; opt_scip_cpu += opt_scip_cpu_add;
                bound_gap = ubound - lbound;
                MY_SCIP_CALL(SCIPsetRealParam(scip, "limits/time", opt_scip_cpu));
                //MY_SCIP_CALL(SCIPrestartSolve(scip));
                if (!solver->ipamir_used || opt_verbosity > 0) 
                    reportf("Restarting SCIP solver (with time-limit = %.0fs) ...\n", opt_scip_cpu);
                try_again = true;
            }
        }
    }
    } while (try_again);

    // release SCIP vars
    for (auto v: vars)
        if (v != nullptr) MY_SCIP_CALL(SCIPreleaseVar(scip, &v));
    vars.clear();

    // if optimum found, exit
    if (found_opt == l_True) {
        std::lock_guard<std::mutex> lck(optsol_mtx);
	char test = OPT_NONE;
        if (opt_finder.compare_exchange_strong(test, OPT_SCIP)) {
	    if (!solver->ipamir_used || opt_verbosity > 0) 
		    reportf("SCIP optimum (rounded): %" PRId64 "\n", best_value);
	    solver->best_goalvalue = best_value;
            vec<lbool> opt_model(scip_model.size()); 
            for (int i = scip_model.size() - 1; i >= 0 ; i--)
                opt_model[i] = (scip_model[i] == l_Undef && !solver->sat_solver.isEliminated(i) ? l_False : scip_model[i]);
            solver->sat_solver.extendGivenModel(opt_model);
            solver->best_model.clear();
            for (int x = 0; x < solver->pb_n_vars; x++) solver->best_model.push(opt_model[x] != l_False);
            Minisat::vec<Lit> soft_unsat; // Not used in this context
            solver->best_goalvalue = (solver->fixed_goalval + evalGoal(solver->soft_cls, solver->best_model, soft_unsat)) * solver->goal_gcd;

	    extern bool opt_satisfiable_out;
	    opt_satisfiable_out = false;

            if (opt_verbosity >= 1) {

              { std::lock_guard<std::mutex> lck(stdout_mtx);
                SCIP_MESSAGEHDLR *mh = SCIPgetMessagehdlr(scip);
                auto mi = mh->messageinfo;
                mh->messageinfo = uwrMessageInfo;
                MY_SCIP_CALL(SCIPsetMessagehdlr(scip, mh));
                printf("c _______________________________________________________________________________\nc \n");
                SCIPprintStatusStatistics(scip, nullptr);
                SCIPprintOrigProblemStatistics(scip, nullptr);
                SCIPprintTimingStatistics(scip, nullptr);
                mh->messageinfo = mi;
                MY_SCIP_CALL(SCIPsetMessagehdlr(scip, mh));
	      }
                solver->printStats(false);
            }
            if (!solver->ipamir_used) {
                outputResult(*solver, true);
		std::this_thread::sleep_for(std::chrono::milliseconds(10));
                //MY_SCIP_CALL(SCIPfree(&scip));
                std::_Exit(30);
            }
        }
    }
    MY_SCIP_CALL(SCIPfree(&scip));
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

lbool MsSolver::scip_solve(const Minisat::vec<Lit> *assump_ps,
                                  const vec<Int> *assump_Cs,
                                  const IntLitQueue *delayed_assump,
                                  bool weighted_instance,
                                  int sat_orig_vars,
                                  int sat_orig_cls,
                                  ScipSolver &scip_solver)
{
    bool res = sat_solver.reduceProblem(); sat_orig_cls = sat_solver.nClauses();
    extern bool opt_force_scip;

    if (!res || !opt_force_scip &&
            (sat_solver.nFreeVars() >= 100000 || sat_orig_cls >= 600000 || soft_cls.size() >=  100000))
        return l_Undef;

    extern double opt_scip_cpu, opt_scip_delay;
    extern bool opt_scip_parallel;
    if (!ipamir_used || opt_verbosity >= 2) reportf("Using SCIP solver, version %.1f.%d, https://www.scipopt.org\n", 
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
    if (opt_verbosity <= 1)
        MY_SCIP_CALL(SCIPsetIntParam(scip, "display/verblevel", 0));

    std::vector<lbool> scip_model(sat_orig_vars);
    for (Var x = sat_orig_vars - 1; x >= 0; x--) scip_model[x] = sat_solver.value(x);

    // 2. create variable(include relax)
    std::vector<SCIP_VAR *> vars(sat_orig_vars, nullptr);
    if (ipamir_used)
        for (int i = 0; i < global_assumptions.size(); i++)
            if (set_scip_var(scip, this, vars, global_assumptions[i]) == l_False) return l_False;

    // 3. add constraint
#ifdef CADICAL
    ScipClauseIterator it(scip, this, vars);
    sat_solver.solver->traverse_clauses(it);
#else
    for (int i = 0; i < sat_orig_cls; i++)
    {
        bool is_satisfied;
        const Minisat::Clause &ps = sat_solver.getClause(i, is_satisfied);
        if (!is_satisfied)
        {
            std::string cons_name = "cons" + std::to_string(i);
            add_constr(scip, this, ps, vars, cons_name);
        }
    }
#endif
    int64_t obj_offset = 0;
    int obj_vars = 0;
    auto set_var_coef = [&vars, &obj_offset, &obj_vars, scip, this](Lit relax, weight_t weight)
    {
        if (value(relax) != l_Undef) {
            if (value(relax) == l_False) obj_offset += fromweight(weight) * fromweight(this->goal_gcd);
        } else {
            obj_vars++;
            weight_t coef = sign(relax) ? weight : -weight;
            coef *= this->goal_gcd;
            if (set_scip_var(scip, this, vars, relax) == l_False) return l_False;
            auto v = vars[var(relax)];
            MY_SCIP_CALL(SCIPaddVarObj(scip, v, double(coef)));
            if (coef < 0)
                obj_offset -= fromweight(coef);
        }
        return l_Undef;
    };
    if (weighted_instance)
    {
        for (int i = 0; i < top_for_strat; ++i)
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
                add_constr(scip, this, ps, vars, cons_name);
            }
        }
    }

    // 4. set objective
    if (opt_verbosity >= 2)
        reportf("SCIPobj: soft_cls.size=%u, assump_ps->size=%u, delayed_assump.size=%u, goal_gcd=%ld, hard_cls=%d\n", 
            top_for_strat, assump_ps->size(), delayed_assump->getHeap().size() - 1, goal_gcd, sat_orig_cls);
    for (int i = 0; i < assump_ps->size(); ++i)
        if (set_var_coef((*assump_ps)[i], tolong((*assump_Cs)[i])) == l_False) return l_False;
    for (int i = 1; i < delayed_assump->getHeap().size(); ++i)
    {
        const Pair<Int, Lit> &weight_lit = delayed_assump->getHeap()[i];
        Lit relax = weight_lit.snd;
        weight_t weight = tolong(weight_lit.fst);
        if (set_var_coef(relax, weight) == l_False) return l_False;
    }
    if (opt_verbosity >= 2)
        reportf("SCIPobj: obj_var=%d, obj_offset=%" PRId64 ", ob_offset_to_add: %ld %ld\n", obj_vars, obj_offset,
                goal_gcd * tolong(fixed_goalval), goal_gcd*tolong(harden_goalval));
    obj_offset += fromweight(goal_gcd) * tolong(fixed_goalval + harden_goalval);

    // 5. do solve
    // MY_SCIP_CALL((SCIPwriteOrigProblem(scip, "1.lp", nullptr, FALSE)));
    // MY_SCIP_CALL((SCIPwriteTransProblem(scip, "2.lp", nullptr, FALSE)));
    if (!ipamir_used || opt_verbosity > 0) reportf("Starting SCIP solver %s (with time-limit = %.0fs) ...\n", 
            (opt_scip_parallel? "in a separate thread" : ""), opt_scip_cpu);

    if (opt_scip_parallel) {
        static auto f = std::async(std::launch::async, 
            scip_solve_async, scip, std::move(vars), std::move(scip_model), this, obj_offset);
        return l_Undef;
    } else if (opt_scip_delay > 0) {
        scip_solver.scip = scip;
        scip_solver.vars = std::move(vars);
        scip_solver.model = std::move(scip_model);
        scip_solver.obj_offset = obj_offset;
        scip_solver.must_be_started = true;
        if (!ipamir_used || opt_verbosity > 0) reportf("SCIP start delayed for at least %.0fs\n", opt_scip_delay);  
        return l_Undef;
    } else
        return scip_solve_async(scip, std::move(vars), std::move(scip_model), this, obj_offset);
}

#endif
