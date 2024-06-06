/******************************************
Copyright (c) 2014, Tomas Balyo, Karlsruhe Institute of Technology.
Copyright (c) 2014, Armin Biere, Johannes Kepler University.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.
***********************************************/

#include "MsSolver.h"
#include "FEnv.h"
#include "Main_utils.h"
#include "Debug.h"
#include "ipamir.h"

extern bool opt_satisfiable_out;
extern time_t wall_clock_time;

struct MySolver {
    ~MySolver()
    {
        delete solver;
    }

    MySolver() : nomodel(true), solving_count(0)
    {
        opt_verbosity = 0;
        solver = new MsSolver(opt_verbosity > 0, true);
        solver->ipamir_used = true;
        opt_maxsat = true, opt_maxsat_msu = true; 
        opt_minimization = 1,  opt_to_bin_search = false;
        opt_convert = opt_convert_goal = ct_Sorters; opt_seq_thres = 4;
        opt_satisfiable_out = false;
#ifdef USE_SCIP
        opt_use_scip_slvr = true; opt_scip_parallel = true;
        opt_scip_cpu = opt_scip_cpu_default; // = 400s
        time(&wall_clock_time);
#endif
        setOptions(0, NULL, false); // read UWrMaxSat options from the UWRFLAGS env variable
    }

    MsSolver* solver;
    vec<Lit>  varmap;
    Map<Lit, uint64_t> new_soft_lit;
    bool nomodel;
    vec<Lit> clause;
    vec<Lit> assumptions;
    int solving_count;
};

extern "C" {

/**
 * Return the name and the version of the incremental MaxSAT solving library.
 */
IPAMIR_API const char * ipamir_signature ()
{
    static char tmp[200] = "UWrMaxSat" UWR_VERSION;
    return tmp;
}

/**
 * Construct a new solver and return a pointer to it.
 * Use the returned pointer as the first parameter in each
 * of the following functions.
 *
 * Required state: N/A
 * State after: INPUT
 */
IPAMIR_API void * ipamir_init ()
{
    increase_stack_size(256);
    MySolver *s = new MySolver;
    pb_solver = s->solver;
    return (void*)s;
}

/**
 * Release the solver, i.e., all its resoruces and
 * allocated memory (destructor). The solver pointer
 * cannot be used for any purposes after this call.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: undefined
 */
IPAMIR_API void ipamir_release (void * solver)
{
    MySolver* s = (MySolver*)solver;
    delete s;
    pb_solver = nullptr;
}

namespace
{
void ensure_var_created(MySolver& s, int32_t var)
{
    pb_solver = s.solver;
    var = abs(var);
    if (var >= s.varmap.size()) 
        s.varmap.growTo(var + 1, lit_Undef);
    if (s.varmap[var] == lit_Undef) {
        Var new_var = s.solver->sat_solver.nVars();
        s.solver->ipamir_vars.set(new_var, true);
        s.varmap[var] = mkLit(new_var, false);
        s.solver->sat_solver.newVar();
        s.solver->sat_solver.setFrozen(new_var, true);
    }
}
}

/**
 * Add the given literal into the currently added hard clause
 * or finalize the clause with a 0.
 * Clauses added by this function cannot be removed. The addition of removable
 * clauses can be simulated using activation literals and assumptions.
 *
 * Required state: INPUT or OPTIMAL or SAT or UNSAT
 * State after: INPUT
 *
 * Literals are encoded as (non-zero) integers as in the DIMACS formats. They
 * have to be smaller or equal to INT32_MAX and strictly larger than INT32_MIN
 * (to avoid negation overflow). This applies to all the literal arguments in
 * API functions.
 */
IPAMIR_API void ipamir_add_hard (void * solver, int32_t lit_or_zero)
{
    MySolver* s = (MySolver*)solver;
    pb_solver = s->solver;

    if (lit_or_zero == 0) {
        s->nomodel = true;
        s->solver->addClause(s->clause);
        if (opt_verbosity > 0 && !s->solver->okay()) reportf("\n***** Hard clause just added makes the instance unsatisfiable *****\n");
        s->clause.clear();
    } else {
        ensure_var_created(*s, lit_or_zero);
        Lit lit = mkLit(var(s->varmap[abs(lit_or_zero)]), lit_or_zero < 0);
        s->clause.push(lit);
    }
}

/**
 * Declare the literal 'lit' soft and set its weight to 'weight'. After calling
 * this function, assigning lit to true incurs cost 'weight'. On a clausal
 * level, this corresponds to adding a unit soft clause containing the negation
 * of 'lit' and setting its weight to 'weight'.
 * 
 * Non-unit soft clauses C of weight w should be normalized by introducing a
 * new literal b, adding (C or b) as a hard clause via 'ipamir_add_hard', and
 * declaring b as a soft literal of weight w.
 * 
 * If 'lit' has already been declared as a soft literal, this function changes the
 * weight of 'lit' to 'weight'.
 *
 * Required state: INPUT or OPTIMAL or SAT or UNSAT
 * State after: INPUT
 */
IPAMIR_API void ipamir_add_soft_lit (void * solver, int32_t lit, uint64_t weight)
{
    MySolver* s = (MySolver*)solver;
    pb_solver = s->solver;
    s->nomodel = true;
    ensure_var_created(*s, lit);
    Lit plit = mkLit(var(s->varmap[abs(lit)]), lit < 0);
    int begin = 0, cnt = s->solver->soft_cls.size(); // binary search for ~plit in the soft_cls vector
    while (cnt > 0) {
        int step = cnt / 2, mid = begin + step;
        if (s->solver->soft_cls[mid].snd->last() < ~plit) begin = mid + 1, cnt -= step + 1; 
        else cnt = step;
    }
    if (begin < s->solver->soft_cls.size() && s->solver->soft_cls[begin].snd->last() == ~plit) {
        s->solver->soft_cls[begin].fst = weight;
    } else
        s->new_soft_lit.set(~plit,weight);
}

/**
 * Add an assumption for the next call of 'ipamir_solve'. After calling
 * 'ipamir_solve' all previously added assumptions are cleared.
 * 
 * Note that on a clausal level, assuming the negation of a soft literal 'lit'
 * (declared via 'ipamir_add_soft_lit') corresponds to hardening a soft clause.
 * 
 * Required state: INPUT or OPTIMAL or SAT or UNSAT
 * State after: INPUT
 */
IPAMIR_API void ipamir_assume (void * solver, int32_t lit)
{
    MySolver* s = (MySolver*)solver;
    pb_solver = s->solver;
    s->nomodel = true;
    ensure_var_created(*s, lit);
    Lit plit = mkLit(var(s->varmap[abs(lit)]), lit < 0);
    s->assumptions.push(plit);
}

/**
 * Solve the MaxSAT instance, as defined by previous calls to 'ipamir_add_hard'
 * and 'ipamir_add_soft_lit', under the assumptions specified by previous calls
 * to 'ipamir_assume' since the last call to 'ipamir_solve'.
 * 
 * A feasible solution is an assignment that satisfies the hard clauses and
 * assumptions. An optimal solution is a solution which minimizes the sum of
 * weights of soft literals set to true.
 * 
 * Return one of the following:
 * 
 * 0 -- If the search is interrupted and no feasible solution has yet been
 * found. The state of the solver is set to INPUT. Note that the solver can only
 * be interrupted via 'ipamir_set_terminate'.
 * 
 * 10 -- If the search is interrupted but a feasible solution has been found
 * before the interrupt occurs. The state of the solver is changed to SAT.
 * 
 * 20 -- If no feasible solution exists. The state of the solver is changed to
 * UNSAT.
 * 
 * 30 -- If an optimal solution is found. The state of the solver is changed to
 * OPTIMAL.
 * 
 * 40 -- If the solver is in state ERROR. The solver enters this state if a
 * sequence of ipamir calls have been made that the solver does not support.
 * 
 * This function can be called in any defined state of the solver. Note that
 * the state of the solver _during_ execution of 'ipamir_solve' is undefined.
 *
 * Required state: INPUT or OPTIMAL or SAT or UNSAT
 * State after: INPUT or OPTIMAL or SAT or UNSAT or ERROR
 */
extern "C++" void clear_shared_formulas();

IPAMIR_API int ipamir_solve (void * solver)
{
    MySolver* s = (MySolver*)solver;
    pb_solver = s->solver;

    //solve
    s->solver->declared_n_vars = s->solver->nVars();
    s->solver->declared_n_constrs = s->solver->nConstrs();

    vec<Lit> soft_lit; // adding new assignments of soft literals
    vec<Lit> cl;
    s->new_soft_lit.domain(soft_lit);
    for (int i = soft_lit.size()-1; i >= 0; i--) {
        cl.push(soft_lit[i]);
        s->solver->storeSoftClause(cl, s->new_soft_lit.at(soft_lit[i]));
        cl.clear();
    }
    s->new_soft_lit.clear();
    s->solver->ipamir_reset(s->assumptions);

    clear_shared_formulas();

    s->solver->maxsat_solve(PbSolver::sc_Minimize);
    s->assumptions.clear();
    s->nomodel = true;
    s->solving_count++;

    if (s->solver->asynch_interrupt) {
        if (s->solver->best_goalvalue != Int_MAX) {
            s->nomodel = false;
            return 10; // SAT
        } else
            return 0;  // UNKNOWN
    } else
        if (s->solver->best_goalvalue != Int_MAX) {
            s->nomodel = false;
            return 30; // OPTIMUM FOUND
        } else
            return 20; // UNSAT
}

/**
 * Retuns the objective value of the current solution, i.e. the sum of weights
 * of all soft literals set to true.
 * 
 * This function can only be used if 'ipamir_solve' has returned 20 or 30, and
 * no 'ipamir_add_hard', 'ipamir_add_soft_lit', or 'ipamir_assume' has been
 * called since then, i.e., the state of the solver is OPTIMAL or SAT.
 * 
 * Required state: OPTIMAL or SAT
 * State after: OPTIMAL or SAT (unchanged)
 */
IPAMIR_API uint64_t ipamir_val_obj (void * solver)
{
    MySolver* s = (MySolver*)solver;
    if (s->nomodel) return 0;
    pb_solver = s->solver;
    char* tmp = toString(s->solver->best_goalvalue);
    int64_t res = strtoull(tmp, nullptr, 10);
    xfree(tmp);
    return res;
}

/**
 * Get the truth value of the given literal in the found solution. Return 'lit'
 * if True, '-lit' if False, and 0 if not important.
 * 
 * This function can only be used if 'ipamir_solve' has returned 20 or 30, and
 * no 'ipamir_add_hard', 'ipamir_add_soft_lit', or 'ipamir_assume' has been
 * called since then, i.e., the state of the solver is OPTIMAL or SAT.
 *
 * Required state: OPTIMAL or SAT
 * State after: OPTIMAL or SAT (unchanged)
 */
IPAMIR_API int32_t ipamir_val_lit (void * solver, int32_t lit)
{
    MySolver* s = (MySolver*)solver;
    if (s->nomodel) return 0;
    pb_solver = s->solver;

    assert(s->solver->okay());

    const int32_t ipamirVar = std::abs(lit);
    Lit plit = s->varmap[ipamirVar];
    if (plit == lit_Undef) return 0;
    const int32_t cmVar = var(plit);
    if (cmVar < 0 || cmVar >= s->solver->best_model.size())
        return 0;
    const bool val = s->solver->best_model[cmVar];
    if (val && lit > 0 || !val && lit < 0)
        return lit;
    else
        return -lit;
}

/**
 * Set a callback function used to indicate a termination requirement to the
 * solver. The solver will periodically call this function and check its return
 * value during the search. The ipamir_set_terminate function can be called in
 * any state of the solver, the state remains unchanged after the call.
 * The callback function is of the form "int terminate(void * state)"
 *   - it returns a non-zero value if the solver should terminate.
 *   - the solver calls the callback function with the parameter "state"
 *     having the value passed in the ipamir_set_terminate function (2nd parameter).
 *
 * Required state: INPUT or OPTIMAL or SAT or UNSAT
 * State after: INPUT or OPTIMAL or SAT or UNSAT (unchanged)
 */
IPAMIR_API void ipamir_set_terminate (void * solver, void * state, int (* terminate)(void *))
{
    MySolver* s = (MySolver*)solver;
    s->solver->termCallbackState = state;
    s->solver->termCallback = terminate;
    s->solver->sat_solver.setTermCallback(state, terminate);
}


}
