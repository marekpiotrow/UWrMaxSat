/**************************************************************************************[PbSolver.h]
Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson

KP-MiniSat+ based on MiniSat+ -- Copyright (c) 2018-2020 Michał Karpiński, Marek Piotrów

UWrMaxSat based on KP-MiniSat+ -- Copyright (c) 2019-2020 Marek Piotrów

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

#ifndef PbSolver_h
#define PbSolver_h

#include <limits>
#include "SatSolver.h"
#include "Map.h"
#include "StackAlloc.h"

#ifdef BIG_WEIGHTS
using weight_t = Int;
#define toweight(x) (x)
#define WEIGHT_MAX Int_MAX
#else
using weight_t = int64_t;
#define toweight(x) tolong(x)
static inline const char *toString(weight_t x) { static char buf[30]; sprintf(buf, "%" PRId64, x); return buf;  }
#define WEIGHT_MAX std::numeric_limits<weight_t>::max()
#endif
#define WEIGHTSUM_MAX Int_MAX

void clear_shared_formulas(void);

DefineHash(Lit, return (uint)toInt(key); )

//=================================================================================================
// Linear -- a class for storing pseudo-boolean constraints:


class Linear {
    int     orig_size;  // Allocated terms in constraint.
public:
    int     size;       // Terms in constraint.
    Int     lo, hi;     // Sum should be in interval [lo,hi] (inclusive).
    Lit     lit;        // Literal implies constraint (lit_Undef for normal case).
private:
    char    data[0];    // (must be last element of the struct)
public:
    // NOTE: Cannot be used by normal 'new' operator!
    Linear(const vec<Lit>& ps, const vec<Int>& Cs, Int low, Int high, Lit ll) {
        orig_size = size = ps.size(), lo = low, hi = high; lit = ll;
        char* p = data;
        for (int i = 0; i < ps.size(); i++) *(Lit*)p = ps[i], p += sizeof(Lit);
        for (int i = 0; i < Cs.size(); i++) new ((Int*)p) Int(Cs[i]), p += sizeof(Int); }

    ~Linear()
    {
        for (int i = 0; i < size; i++)
            (*this)(i).~Int();
    }

    Lit operator [] (int i) const { return *(Lit*)(data + sizeof(Lit)*i); }
    Int operator () (int i) const { return *(Int*)(data + sizeof(Lit)*orig_size + sizeof(Int)*i); }
    Lit& operator [] (int i) { return *(Lit*)(data + sizeof(Lit)*i); }
    Int& operator () (int i) { return *(Int*)(data + sizeof(Lit)*orig_size + sizeof(Int)*i); }
};


//=================================================================================================
// PbSolver -- Pseudo-boolean solver (linear boolean constraints):


class PbSolver {
public:
    ExtSimpSolver       sat_solver;     // Underlying SAT solver.
protected:
    vec<Lit>            trail;          // Chronological assignment stack.

    StackAlloc<char*>   mem;            // Used to allocate the 'Linear' constraints stored in 'constrs' (other 'Linear's, such as the goal function, are allocated with 'xmalloc()')

public:
    vec<Linear*>        constrs;        // Vector with all constraints.
    Linear*             goal;           // Non-normalized goal function (used in optimization). NULL means no goal function specified. NOTE! We are always minimizing.
    Int                 LB_goalvalue, UB_goalvalue;  // Lower and upper bounds on the goal value
    vec<Minisat::Lit>   base_assump;    // Used to efficiently encode (using sorters) changing goal bounds in binary search 
    bool                statsPrinted;

protected:
    vec<int>            n_occurs;       // Lit -> int: Number of occurrences.
    vec<vec<int> >      occur;          // Lit -> vec<int>: Occur lists. Left empty until 'setupOccurs()' is called.

    int                 propQ_head;     // Head of propagation queue (index into 'trail').
    Minisat::vec<Lit>   tmp_clause;

    // Main internal methods:
    //
    bool    propagate(Linear& c);
    void    propagate();
    virtual bool    addUnit  (Lit p) {
        if (value(p) == l_Undef) trail.push(p);
        return sat_solver.addClause(p); }
public:
    bool    addClause(const vec<Lit>& ps){
        tmp_clause.clear(); for (int i = 0; i < ps.size(); i++) tmp_clause.push(ps[i]);
        return sat_solver.addClause_(tmp_clause); }
protected:        
    bool    normalizePb(vec<Lit>& ps, vec<Int>& Cs, Int& C, Lit& lit);
    void    storePb   (const vec<Lit>& ps, const vec<Int>& Cs, Int lo, Int hi, Lit lit);
    void    setupOccurs();   // Called on demand from 'propagate()'.
    void    findIntervals();
    bool    rewriteAlmostClauses();
public:
    bool    convertPbs(bool first_call);   // Called from 'solve()' to convert PB constraints to clauses.

public:
    PbSolver(bool print_info = true, bool use_preprocessing = false) 
                : sat_solver(print_info)
                , goal(NULL)
                , LB_goalvalue(Int_MIN)
                , UB_goalvalue(Int_MAX)
                , statsPrinted(false)
                , propQ_head(0)
                //, stats(sat_solver.stats_ref())
                , declared_n_vars(-1)
                , declared_n_constrs(-1)
                , totalSorters(0), totalSorterInputs(0.0), totalReusedInputs(0.0), totalReusedPercent(0.0)
                , best_goalvalue(Int_MAX)
                , asynch_interrupt(false)
                , cpu_interrupt(false)
                , use_base_assump(false)
                {
                    // Turn off preprocessing if wanted.
                    if (!use_preprocessing) 
                        sat_solver.eliminate(true); 
                }
    void reset() {
        trail.clear(); mem.clear(); constrs.clear();
        LB_goalvalue = Int_MIN; UB_goalvalue = Int_MAX;
        propQ_head = 0; statsPrinted = false;
        best_goalvalue = Int_MAX;

    }

    // Helpers (semi-internal):
    //
    virtual lbool   value(Var x) const { return sat_solver.value(x); }
    virtual lbool   value(Lit p) const { return sat_solver.value(p); }
    int     nVars()      const { return sat_solver.nVars(); }
    int     nClauses()   const { return sat_solver.nClauses(); }
    int     nConstrs()   const { return constrs.size(); }

    // Public variables:
    //BasicSolverStats& stats;
    void    printStats(bool printSatStats = true);

    int     declared_n_vars;            // Number of variables declared in file header (-1 = not specified).
    int     declared_n_constrs;         // Number of constraints declared in file header (-1 = not specified).
    int     pb_n_vars;                  // Actual number of variables (before clausification).
    int     pb_n_constrs;               // Actual number of constraints (before clausification).

    int     totalSorters;               // The total number of encoded sorters.
    double  totalSorterInputs, totalReusedInputs, totalReusedPercent; // Counters to print statistics of the reuse of encoded sorters. 

    Map<cchar*, int>    name2index;
    vec<cchar*>         index2name;
    vec<bool>           best_model;     // Best model found (size is 'pb_n_vars').
    Int                 best_goalvalue; // Value of goal function for that model (or 'Int_MAX' if no models were found).
    bool                asynch_interrupt, cpu_interrupt, use_base_assump;

    // Problem specification:
    //
    int     getVar         (cchar* name);
    void    allocConstrs   (int n_vars, int n_constrs);
    void    addGoal        (const vec<Lit>& ps, const vec<Int>& Cs);
    bool    addConstr      (const vec<Lit>& ps, const vec<Int>& Cs, Int rhs, int ineq, Lit& lit);

    // Solve:
    //
    bool    okay(void) { return sat_solver.okay(); }

    enum solve_Command { sc_Minimize, sc_FirstSolution, sc_AllSolutions };
    void    solve(solve_Command cmd = sc_Minimize);        // Returns best/first solution found or Int_MAX if UNSAT.
};


//=================================================================================================
#endif
