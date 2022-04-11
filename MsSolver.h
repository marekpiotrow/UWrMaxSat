/**************************************************************************************[MsSolver.h ]
  Copyright (c) 2018-2019, Marek Piotrów

  Based on PbSolver.h ( Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson)

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

#ifndef MsSolver_h
#define MsSolver_h

#include "PbSolver.h"
#include "VecMaps.h"
#include "Sort.h"

Int evalGoal(const vec<Pair<weight_t, Minisat::vec<Lit>* > >& soft_cls, vec<bool>& model, Minisat::vec<Lit>& soft_unsat);

static inline int hleft (int i)  { return i * 2; }
static inline int hright(int i)  { return i * 2 + 1; }
static inline int hparent(int i) { return i / 2; }

class IntLitQueue {
  private:
    vec<Pair<Int, Lit> > heap;

    bool cmp(int x, int y) { 
        return heap[x].fst > heap[y].fst /*|| heap[x].fst == heap[y].fst && heap[x].snd > heap[y].snd*/; }

  public:
    IntLitQueue() { heap.push(Pair_new(1, lit_Undef)); }

    bool empty() { return heap.size() <= 1; }

    int size() { return heap.size(); }

    const vec<Pair<Int, Lit> >& getHeap() const { return heap; }

    void clear() { heap.shrink(heap.size() - 1); }

    const Pair<Int, Lit>& top() { return heap[1]; }

    void push(Pair<Int, Lit> p) { 
        heap.push();
        int i = heap.size() - 1;
        heap[0] = std::move(p);
        while (hparent(i) != 0 && cmp(0, hparent(i))) { // percolate up
            heap[i] = std::move(heap[hparent(i)]);
            i       = hparent(i);
        }
        heap[i] = std::move(heap[0]);
    }

    void pop(void) {
        heap[1] = std::move(heap.last());
        heap.pop();
        if (heap.size() > 1) { // percolate down
            int i = 1;
            heap[0] = std::move(heap[1]);
            while (hleft(i) < heap.size()){
                int child = hright(i) < heap.size() && cmp(hright(i), hleft(i)) ? hright(i) : hleft(i);
                if (!cmp(child, 0)) break;
                heap[i] = std::move(heap[child]);
                i       = child;
            }
            heap[i] = std::move(heap[0]);
        }
    }

} ;

#ifdef USE_SCIP
//#include <vector>
//#include <algorithm>
#include <scip/scip.h>
#include <scip/scipdefplugins.h>
#endif

class MsSolver final : public PbSolver {
  public:
    MsSolver(bool use_preprocessing = false) : 
          PbSolver(use_preprocessing)
        , ipamir_used(false)
        , harden_goalval(0)
        , fixed_goalval(0)
        , goal_gcd(1)
        , max_input_lit(lit_Undef)  {}

    bool                ipamir_used;
    Int                 harden_goalval,  //  Harden goalval used in the MaxSAT preprocessing 
                        fixed_goalval;   // The sum of weights of soft clauses that must be false
    vec<Pair<weight_t, Minisat::vec<Lit>* > > orig_soft_cls; // Soft clauses before preprocessing by MaxPre; empty if MaxPre is not used
    vec<Pair<weight_t, Minisat::vec<Lit>* > > soft_cls; // Relaxed non-unit soft clauses with weights; a relaxing var is the last one in a vector. 
    weight_t            goal_gcd; // gcd of soft_cls weights
    int                 top_for_strat, top_for_hard; // Top indices to soft_cls for stratification and hardening operations.
    Map<Lit, Int>       harden_lits;    // The weights of literals included into "At most 1" clauses (MaxSAT preprocessing of soft clauese).
    vec<Pair<Lit,Int> > am1_rels;       // The weights of relaxing vars in "At most 1" clauses
    vec<Lit>            harden_assump;  // If IPAMIR interface is used, harden soft literals are put here instead of creating unit clauses
    vec<Lit>            global_assumptions; // If IPAMIR interface is used, sorted literals used in IPAMIR assumptions are in this vector
    BitMap              global_assump_vars, // If IPAMIR interface is used, variables used in the global_assumptions are in this map
                        ipamir_vars;    // If IPAMIR interface is used, variables created in the interface are in this map
    Lit                 max_input_lit;  // If IMPAMIR interface is not used, the maximal value of literals created during reading an instance

    void ipamir_reset(const vec<Lit>& assumptions) {
        PbSolver::reset();
        harden_goalval = fixed_goalval = 0;
        goal_gcd = 1;
        harden_lits.clear(); am1_rels.clear(); harden_assump.clear();
        assumptions.copyTo(global_assumptions);
        global_assump_vars.clear();
        if (global_assumptions.size() > 0) {
            Sort::sort(global_assumptions);
            for (int i =0; i < global_assumptions.size(); i++) global_assump_vars.set(var(global_assumptions[i]), true);
        }
        //FEnv::stack.clear();
    }

    bool    is_input_var(Lit p) {
        return !ipamir_used && p <= max_input_lit || ipamir_used && ipamir_vars.at(var(p));
    }

    bool    addUnitClause(Lit p) {
        bool res = true;
        if (ipamir_used) harden_assump.push(p);
        else res = sat_solver.addClause(p); 
        return res; 
    }
    virtual lbool   value(Var x) const { return sat_solver.value(x); }
    virtual lbool   value(Lit p) const { return sat_solver.value(p); }
    bool    addUnit  (Lit p) {
        if (value(p) == l_Undef) trail.push(p);
        return addUnitClause(p);
    }
    void    storeSoftClause(const vec<Lit>& ps, weight_t weight) {
                Minisat::vec<Lit> *ps_copy = new Minisat::vec<Lit>; 
                for (int i = 0; i < ps.size(); i++) ps_copy->push(ps[i]); 
                soft_cls.push(Pair_new(weight, ps_copy)); }

    void    harden_soft_cls(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs, vec<weight_t>& sorted_assump_Cs, IntLitQueue& delayed_assump, Int& delayed_assump_sum);
    void    optimize_last_constraint(vec<Linear*>& constrs, Minisat::vec<Lit>& assump_ps, Minisat::vec<Lit>& new_assump);

#ifdef USE_SCIP
    bool scip_solve(const Minisat::vec<Lit> *assump_ps, const vec<Int> *assump_Cs, const IntLitQueue *delayed_assump,
            bool weighted_instance, int sat_orig_vars, int sat_orig_cls);
#endif    

    lbool   satSolveLimited(Minisat::vec<Lit> &assump_ps);
    void    maxsat_solve(solve_Command cmd = sc_Minimize); 
    void    preprocess_soft_cls(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs, const Int& max_assump_Cs, 
                                           IntLitQueue& delayed_assump, Int& delayed_assump_sum);
} ;

#endif
