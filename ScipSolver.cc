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

std::atomic<bool> SCIP_found_opt(false);

template<class T>
SCIP_RETCODE add_constr(SCIP *scip,
                        MsSolver *solver,
                        const T &ps,
                        const std::vector<SCIP_VAR *> &vars,
                        const std::string &const_name)
{
    SCIP_CONS *cons = nullptr;
    SCIP_CALL(SCIPcreateConsBasicLinear(scip, &cons, const_name.c_str(), 0, nullptr, nullptr, 0, SCIPinfinity(scip)));
    int lhs = 1;
    for (int j = 0; j < ps.size(); j++)
    {
        auto lit = ps[j];
        if (solver->value(lit) != l_Undef) continue;
        auto v = vars[var(lit)];
        SCIP_CALL(SCIPaddCoefLinear(scip, cons, v, sign(lit) ? -1 : 1));
        if (sign(lit))
            lhs--;
    }
    SCIP_CALL(SCIPchgLhsLinear(scip, cons, lhs));
    SCIP_CALL(SCIPaddCons(scip, cons));
    SCIP_CALL(SCIPreleaseCons(scip, &cons));
    return SCIP_OKAY;
}

bool scip_solve_async(SCIP *scip, std::vector<SCIP_VAR *> vars, MsSolver *solver)
{
    bool found_opt = false;

    SCIP_CALL(SCIPsolve(scip));
    if (SCIP_STATUS_OPTIMAL == SCIPgetStatus(scip))
    {
        found_opt = true;
        SCIP_SOL *sol = SCIPgetBestSol(scip);
        assert(sol != NULL);
        // SCIP_CALL(SCIPprintSol(scip, sol, NULL, FALSE));
        SCIP_found_opt = true;
        solver->best_goalvalue = long(round(SCIPgetSolOrigObj(scip, sol)));
        reportf("SCIP optimum = %ld\n", tolong(solver->best_goalvalue));
        solver->best_model.clear();
        for (Var x = 0; x < solver->pb_n_vars; x++)
        {
            SCIP_Real v = SCIPgetSolVal(scip, sol, vars[x]);
            solver->best_model.push(v > 0.5);
        }
        extern bool opt_satisfiable_out;
        opt_satisfiable_out = false;
    } else
        reportf("SCIP timeout\n");

    // 6. release
    for (auto v: vars)
        SCIP_CALL(SCIPreleaseVar(scip, &v));
    vars.clear();
    SCIP_CALL(SCIPfree(&scip));

    // 7. if optimum found, exit
    if (found_opt) {
        if (opt_verbosity >= 1) {
            reportf("_______________________________________________________________________________\n\n");
            solver->printStats();
            reportf("_______________________________________________________________________________\n");
        }
        outputResult(*solver, true);
        quick_exit(0);
    }
    return found_opt;
}


bool MsSolver::scip_solve(const Minisat::vec<Lit> *assump_ps,
                                  const vec<Int> *assump_Cs,
                                  const IntLitQueue *delayed_assump,
                                  bool weighted_instance,
                                  int sat_orig_vars,
                                  int sat_orig_cls)
{
    if (sat_orig_vars >= 100000 || sat_orig_cls >= 100000 || soft_cls.size() >=  100000) return false;

    extern double opt_scip_cpu;
    extern bool opt_scip_parallel;
    reportf("Using SCIP solver, version %.1f.%d, https://www.scipopt.org\n", 
            SCIPversion(), SCIPtechVersion());

    // 1. create scip context object
    SCIP *scip = nullptr;
    SCIP_CALL(SCIPcreate(&scip));
    SCIP_CALL(SCIPincludeDefaultPlugins(scip));
    SCIP_CALL(SCIPcreateProbBasic(scip, "UWrMaxSat"));
    if (opt_scip_cpu > 0) 
        SCIP_CALL(SCIPsetRealParam(scip, "limits/time", opt_scip_cpu));
    if (opt_verbosity <= 1)
        SCIP_CALL(SCIPsetIntParam(scip, "display/verblevel", 0));

    // 2. create variable(include relax)
    std::vector<SCIP_VAR *> vars;
    for (Var v = 0; v < sat_orig_vars; ++v)
    {
        SCIP_VAR *var = nullptr;
        std::string name = "x" + std::to_string(v + 1);
        SCIP_Real lb = 0, ub = 1;
        if (value(v) == l_False) ub = 0;
        else if (value(v) == l_True) lb = 1;
        SCIP_CALL(SCIPcreateVarBasic(scip, &var, name.c_str(), lb, ub, 0, SCIP_VARTYPE_BINARY));
        SCIP_CALL(SCIPaddVar(scip, var));
        vars.push_back(var);
    }

    // 3. add constraint
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
    weight_t obj_offset = 0;
    int obj_vars = 0;
    auto set_var_coef = [&vars, &obj_offset, &obj_vars, scip, this](Lit relax, weight_t weight, bool singleton)
    {
        if (singleton && value(relax) != l_Undef) {
            if (value(relax) == l_False) obj_offset += weight;
        } else {
            obj_vars++;
            weight_t coef = sign(relax) ? weight : -weight;
            coef *= this->goal_gcd;
            SCIP_CALL(SCIPaddVarObj(scip, vars[var(relax)], double(coef)));
            if (coef < 0)
                obj_offset -= coef;
        }
        return SCIP_OKAY;
    };
    if (weighted_instance)
    {
        for (int i = 0; i < top_for_strat; ++i)
        {
            const Pair<weight_t, Minisat::vec<Lit> *> &weight_ps = soft_cls[i];
            const Minisat::vec<Lit> &ps = *(weight_ps.snd);
            auto relax = ps.last();
            bool singleton = true;
            if (ps.size() > 1) relax = ~relax, singleton = false;
            weight_t weight = weight_ps.fst;
            set_var_coef(relax, weight, singleton);
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
        set_var_coef((*assump_ps)[i], tolong((*assump_Cs)[i]), false);
    for (int i = 1; i < delayed_assump->getHeap().size(); ++i)
    {
        const Pair<Int, Lit> &weight_lit = delayed_assump->getHeap()[i];
        Lit relax = weight_lit.snd;
        weight_t weight = tolong(weight_lit.fst);
        set_var_coef(relax, weight, false);
    }
    // create a var for the fixed part of objective
    if (opt_verbosity >= 2)
        reportf("SCIPobj: obj_var=%d, obj_offset=%ld, lower_bound=%ld\n", obj_vars, obj_offset, goal_gcd * tolong(LB_goalvalue));
    obj_offset += goal_gcd * tolong(LB_goalvalue);
    if (obj_offset != 0)
    {
        SCIP_VAR *var = nullptr;
        SCIP_CALL(SCIPcreateVarBasic(scip, &var, "obj_offset", 1, 1, double(obj_offset), SCIP_VARTYPE_BINARY));
        SCIP_CALL(SCIPaddVar(scip, var));
        vars.push_back(var);
    }

    // 5. do solve
    // SCIP_CALL((SCIPwriteOrigProblem(scip, "1.lp", nullptr, FALSE)));
    // SCIP_CALL((SCIPwriteTransProblem(scip, "2.lp", nullptr, FALSE)));
    reportf("Starting SCIP solver %s (with time-limit = %.0fs) ...\n", (opt_scip_parallel? "in a separate thread" : ""), opt_scip_cpu);

    static auto f = std::async((opt_scip_parallel ? std::launch::async : std::launch::deferred), 
            scip_solve_async, scip, std::move(vars), this);

    auto b = opt_scip_parallel ? true : f.get();
    return b;
}
#endif
