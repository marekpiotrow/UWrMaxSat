/**************************************************************************************[MsSolver.cc]
  Copyright (c) 2018-2019, Marek Piotrów

  Based on PbSolver.cc ( Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson)

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

#include <unistd.h>
#include <signal.h>
#include "System.h"
#include "Sort.h"
#include "Debug.h"

template<typename int_type>
static int_type gcd(int_type small, int_type big) {
    if (small < 0) small = -small;
    if (big < 0) big = -big;
    return (small == 0) ? big: gcd(big % small, small); }

template<typename T>
static int bin_search(const Minisat::vec<T>& seq, const T& elem)
{
    int fst = 0, cnt = seq.size();
    while (cnt > 0) {
        int step = cnt / 2, mid = fst + step;
        if (seq[mid] < elem) fst = mid + 1, cnt -= step + 1; 
        else cnt = step;
    }
    return (fst < seq.size() && seq[fst] == elem ? fst : -1);
}
        
template<typename T>
static int bin_search(const vec<T>& seq, const T& elem)
{
    int fst = 0, cnt = seq.size();
    while (cnt > 0) {
        int step = cnt / 2, mid = fst + step;
        if (seq[mid] < elem) fst = mid + 1, cnt -= step + 1; 
        else cnt = step;
    }
    return (fst < seq.size() && seq[fst] == elem ? fst : -1);
}
        
static MsSolver *pb_solver;
static
void SIGINT_interrupt(int signum) { 
    pb_solver->sat_solver.interrupt(); pb_solver->asynch_interrupt=true; 
#ifdef SIGXCPU    
    pb_solver->cpu_interrupt = (signum == SIGXCPU);
#else
    (void) signum;
    pb_solver->cpu_interrupt = false;
#endif
}

extern int verbosity;

static void clear_assumptions(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs)
{
    int removed, j = 0;
    for (int i = 0; i < assump_ps.size(); i++) {
        if (assump_Cs[i] < 0) continue;
        if (j < i) assump_ps[j] = assump_ps[i], assump_Cs[j] = assump_Cs[i];
        j++;
    }
    if ((removed = assump_ps.size() - j) > 0)
        assump_ps.shrink(removed), assump_Cs.shrink(removed);
}

static
bool satisfied_soft_cls(Minisat::vec<Lit> *cls, vec<bool>& model)
{
    assert(cls != NULL);
    for (int i = cls->size() - 2; i >= 0; i--)
        if ((( sign((*cls)[i]) && !model[var((*cls)[i])]) 
          || (!sign((*cls)[i]) &&  model[var((*cls)[i])])))
            return true;
    return false;
}


Int evalGoal(const vec<Pair<weight_t, Minisat::vec<Lit>* > >& soft_cls, vec<bool>& model, 
        Minisat::vec<Lit>&soft_unsat)
{
    Int sum = 0;
    bool sat = false;
    soft_unsat.clear();
    for (int i = 0; i < soft_cls.size(); i++) {
        Lit p = soft_cls[i].snd->last(); if (soft_cls[i].snd->size() == 1) p = ~p;
        assert(var(p) < model.size());
        if ((( sign(p) && !model[var(p)]) || (!sign(p) &&  model[var(p)])) 
            && !(sat = satisfied_soft_cls(soft_cls[i].snd, model))) {
            if (opt_output_top > 0) soft_unsat.push(~p);
            sum += soft_cls[i].fst;
        } else if (opt_output_top > 0) {
            soft_unsat.push(p);
        }
        if (sat) { sat = false; model[var(p)] = !model[var(p)]; }
    }
    return sum;
}

static
void core_minimization(SimpSolver &sat_solver, Minisat::vec<Lit> &mus)
{
    int last_size = sat_solver.conflict.size();

    sat_solver.setConfBudget(1000);
    int verb = sat_solver.verbosity; sat_solver.verbosity = 0;
    for (int i = 0; last_size > 1 && i < last_size; ) {
        Lit p = mus[i];
        for (int j = i+1; j < last_size; j++) mus[j-1] = mus[j];
        mus.pop();
        if (sat_solver.solveLimited(mus) != l_False) {
            mus.push();
            for (int j = last_size - 1; j > i; j--) mus[j] = mus[j-1];
            mus[i] = p; i++;
        } else last_size--;
    }
    sat_solver.budgetOff(); sat_solver.verbosity = verb;

    for (int i = mus.size() - 1; i >= 0; i--) mus[i] = ~mus[i];
}

/*static void core_trimming(SimpSolver &sat_solver, int max_size, int n)
{
    int last_size = sat_solver.conflict.size();
    Minisat::vec<Lit> assump(last_size);
    for (int i = n; i > 0 && last_size > max_size; i--) {
        assump.clear();
        for (int j = 0; j < last_size; j++) assump.push(~sat_solver.conflict[j]);
        sat_solver.solve(assump);
        if (sat_solver.conflict.size() >= last_size) return;
        last_size = sat_solver.conflict.size();
    }
}*/

static Int next_sum(Int bound, const vec<Int>& cs)
{ // find the smallest sum of a subset of cs that is greater that bound
    vec<Int> sum[2];
    Int x, next_min = Int_MAX;
    int oldv =0, newv = 1, lst = 0;

    sum[oldv].push(0); ++bound;
    for (int sz = 1, j = 0; j < cs.size(); j++, oldv = newv, newv = 1-oldv, lst = 0) {
        for (int i = 0; i < sz; i++)
            if ((x = sum[oldv][i] + cs[j]) < bound) {
                while (lst < sz && sum[oldv][lst] > x) sum[newv].push(sum[oldv][lst++]);
                if (lst == sz || sum[oldv][lst] < x) sum[newv].push(x);
            } else if (x < next_min) {
                if (x == bound) return x;
                next_min = x;
            }
        while (lst < sz) sum[newv].push(sum[oldv][lst++]);
        sz = sum[newv].size(); sum[oldv].clear();
    }
    return (next_min == Int_MAX ? bound - 1 : next_min);

}

/*static
Int evalPsCs(vec<Lit>& ps, vec<Int>&Cs, vec<bool>& model)
{
    Int sum = 0;
    assert(ps.size() == Cs.size());
    for (int i = 0; i < ps.size(); i++){
        if (( var(ps[i]) >= model.size())
        ||  ( sign(ps[i]) && model[var(ps[i])] == false)
        ||  (!sign(ps[i]) && model[var(ps[i])] == true )
        )
            sum += Cs[i];
    }
    return sum;
}

static
Int evalPsCs(vec<Lit>& ps, vec<Int>&Cs, Minisat::vec<lbool>& model)
{
    Int sum = 0;
    assert(ps.size() == Cs.size());
    for (int i = 0; i < ps.size(); i++){
        if (( sign(ps[i]) && model[var(ps[i])] == l_False)
        ||  (!sign(ps[i]) && model[var(ps[i])] == l_True )
        )
            sum += Cs[i];
    }
    return sum;
}

static void opt_stratification(vec<weight_t>& sorted_assump_Cs, vec<Pair<Int, bool> >& sum_sorted_soft_cls)
{
    assert(sorted_assump_Cs.size() == sum_sorted_soft_cls.size());

    int m = max(1, sum_sorted_soft_cls.size() - 10);
    if (m < 10) m = 1;
    for (int i = sum_sorted_soft_cls.size() - 1; i >= m; i--)
        if (sorted_assump_Cs[i] > sorted_assump_Cs[i-1] + 1 || 
                i < sum_sorted_soft_cls.size() - 1 && !sum_sorted_soft_cls[i + 1].snd) 
            sum_sorted_soft_cls[i].snd = true;
    if (m == 1) return;
    vec<Pair<weight_t, int> > gaps;
    for (int i = 0; i < m; i++) gaps.push(Pair_new(sorted_assump_Cs[i+1] - sorted_assump_Cs[i], i + 1));
    sort(gaps);
    for (int i = gaps.size() - 1, j = 0; j < 10; j++, i--) sum_sorted_soft_cls[gaps[i].snd].snd = true;
}*/

template <class T> struct LT {bool operator()(T x, T y) { return x.snd->last() < y.snd->last(); }};

static weight_t do_stratification(SimpSolver& S, vec<weight_t>& sorted_assump_Cs, vec<Pair<weight_t,
        Minisat::vec<Lit>* > >& soft_cls, int& top_for_strat, Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs)
{
    weight_t  max_assump_Cs;
    max_assump_Cs = sorted_assump_Cs.last(); sorted_assump_Cs.pop();
    if (sorted_assump_Cs.size() > 0 && sorted_assump_Cs.last() == max_assump_Cs - 1) 
        max_assump_Cs = sorted_assump_Cs.last(), sorted_assump_Cs.pop(); 
    int start = top_for_strat - 1;
    while (start >= 0 && soft_cls[start].fst >= max_assump_Cs) start--;
    start++;
    if (start < top_for_strat) {
        int sz = top_for_strat - start, to = 0, fr = sz;
        sort(&soft_cls[start], sz, LT<Pair<weight_t, Minisat::vec<Lit>*> >());
        assump_ps.growTo(assump_ps.size() + sz); assump_Cs.growTo(assump_Cs.size() + sz);
        for (int i = assump_ps.size() - 1; i >= sz; i--)
            assump_ps[i] = assump_ps[i-sz], assump_Cs[i] = assump_Cs[i-sz];
        for (int i = start; i < top_for_strat; i++) {
            Lit p = ~soft_cls[i].snd->last();
            if (soft_cls[i].snd->size() > 1) S.addClause(*soft_cls[i].snd); else p = ~p;
            while (fr < assump_ps.size() && assump_ps[fr] <= p)
                assump_ps[to] = assump_ps[fr], assump_Cs[to++] = assump_Cs[fr++];
            assump_ps[to] = p; assump_Cs[to++] = soft_cls[i].fst;
        }
        sort(&soft_cls[start], sz);
        top_for_strat = start;
    }
    return max_assump_Cs;
}

void MsSolver::harden_soft_cls(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs)
{
    int cnt_unit = 0, cnt_assump = 0, sz = 0;
    Int Ibound = UB_goalvalue - LB_goalvalue, WMAX = Int(WEIGHT_MAX);
    weight_t       wbound = (Ibound >= WMAX ? WEIGHT_MAX : tolong(Ibound));
    weight_t ub_goalvalue = (UB_goalvalue >= WMAX ? WEIGHT_MAX : tolong(UB_goalvalue - fixed_goalval));
    for (int i = top_for_hard - 1; i >= 0 && soft_cls[i].fst > wbound; i--) { // hardening soft clauses with weights > the current goal interval length 
        if (soft_cls[i].fst > ub_goalvalue) sz++;
        Lit p = soft_cls[i].snd->last(); if (soft_cls[i].snd->size() > 1) p = ~p;
        int j = bin_search(assump_ps, p);
        if (j >= 0 && assump_Cs[j] > Ibound) {
            if (opt_minimization == 1) harden_lits.set(p, Int(soft_cls[i].fst));
            assump_Cs[j] = -assump_Cs[j]; // mark a corresponding assumption to be deleted
            cnt_assump++; cnt_unit++; sat_solver.addClause(p);
        } else if (soft_cls[i].fst > ub_goalvalue) { 
            if (opt_minimization == 1) harden_lits.set(p, Int(soft_cls[i].fst));
            cnt_unit++, sat_solver.addClause(p);
        }
    }
    if (opt_verbosity >= 2 && cnt_unit > 0) reportf("Hardened %d soft clauses\n", cnt_unit);
    if (sz > 0 ) top_for_hard -= sz;
    if (cnt_assump > 0) clear_assumptions(assump_ps, assump_Cs);
}

void MsSolver::optimize_last_constraint(vec<Linear*>& constrs, Minisat::vec<Lit>& assump_ps, Minisat::vec<Lit>& new_assump)
{
    Minisat::vec<Lit> assump;
    if (constrs.size() == 0) return ;
    int verb = sat_solver.verbosity; sat_solver.verbosity = 0;
    bool found = false;

    sat_solver.setConfBudget(1000);
    if (sat_solver.solveLimited(assump_ps) == l_False) {
        for (int i=0; i < sat_solver.conflict.size(); i++)
            if (assump_ps.last() == ~sat_solver.conflict[i]) { found = true; break;}
        if (found) {
            if (constrs.size() > 1) {
                constrs[0] = constrs.last();
                constrs.shrink(constrs.size() - 1);
            }
            while (found && (constrs[0]->lo > 1 || constrs[0]->hi < constrs[0]->size - 1)) {
                if (constrs[0]->lo > 1) --constrs[0]->lo; else ++constrs[0]->hi;
                constrs[0]->lit = lit_Undef;
                convertPbs(false);
                Lit newp = constrs[0]->lit;
                sat_solver.setFrozen(var(newp),true);
                sat_solver.addClause(~assump_ps.last(), newp);
                new_assump.push(assump_ps.last()); assump_ps.last() = newp;
                if (sat_solver.solveLimited(assump_ps) != l_False) break;
                found = false;
                for (int i=0; i < sat_solver.conflict.size(); i++)
                    if (assump_ps.last() == ~sat_solver.conflict[i]) { found = true; break;}
            }
        }
    }
    sat_solver.budgetOff(); sat_solver.verbosity = verb;
}

static inline int log2(int n) { int i=0; while (n>>=1) i++; return i; }

void MsSolver::maxsat_solve(solve_Command cmd)
{
    if (!okay()) {
        if (opt_verbosity >= 1) sat_solver.printVarsCls();
        return;
    }
#if defined(GLUCOSE3) || defined(GLUCOSE4)    
    if (opt_verbosity >= 1) sat_solver.verbEveryConflicts = 100000;
    sat_solver.setIncrementalMode();
#endif
    if (soft_cls.size() == 0) { opt_maxsat_msu = false; solve(cmd); return; }
    // Convert constraints:
    pb_n_vars = nVars();
    pb_n_constrs = nClauses();
    if (constrs.size() > 0) {
        if (opt_verbosity >= 1)
            reportf("Converting %d PB-constraints to clauses...\n", constrs.size());
        propagate();
        if (!convertPbs(true)){
            if (opt_verbosity >= 1) sat_solver.printVarsCls(constrs.size() > 0);
            assert(!okay()); return;
        }
        if (opt_convert_goal != ct_Undef)
            opt_convert = opt_convert_goal;
    }

    // Freeze goal function variables (for SatELite):
    for (int i = 0; i < soft_cls.size(); i++) {
        sat_solver.setFrozen(var(soft_cls[i].snd->last()), true);
        if (opt_output_top > 0)
            for (int j = soft_cls[i].snd->size() - 2; j >= 0; j--) 
                sat_solver.setFrozen(var((*soft_cls[i].snd)[j]), true);
    }
    sat_solver.verbosity = opt_verbosity - 1;

    goal_gcd = soft_cls[0].fst;
    for (int i = 1; i < soft_cls.size() && goal_gcd != 1; ++i) goal_gcd = gcd(goal_gcd, soft_cls[i].fst);
    if (goal_gcd != 1) {
        if (LB_goalvalue != Int_MIN) LB_goalvalue /= Int(goal_gcd);
        if (UB_goalvalue != Int_MAX) UB_goalvalue /= Int(goal_gcd);
    }

    assert(best_goalvalue == Int_MAX);

    opt_sort_thres *= opt_goal_bias;
    opt_shared_fmls = true;

    if (opt_cnf != NULL)
        reportf("Exporting CNF to: \b%s\b\n", opt_cnf),
        sat_solver.toDimacs(opt_cnf),
        exit(0);

    pb_solver = this;
    signal(SIGINT, SIGINT_interrupt);
#ifdef SIGXCPU
    signal(SIGXCPU,SIGINT_interrupt);
#endif

    Map<int,int> assump_map(-1);
    vec<Linear*> saved_constrs;
    vec<Lit> goal_ps;
    Minisat::vec<Lit> assump_ps;
    vec<Int> assump_Cs, goal_Cs, saved_constrs_Cs;
    vec<weight_t> sorted_assump_Cs;
    vec<Pair<Int, bool> > sum_sorted_soft_cls;
    bool    sat = false, weighted_instance = true;
    Lit assump_lit = lit_Undef, max_assump = lit_Undef;
    Int     try_lessthan = opt_goal, max_assump_Cs = Int_MIN;
    int     n_solutions = 0;    // (only for AllSolutions mode)
    vec<Pair<Lit,int> > psCs;
    vec<int8_t> multi_level_opt;
    bool opt_delay_init_constraints = false, 
         opt_core_minimization = (nClauses() > 0 || soft_cls.size() < 100000);
    IntLitQueue delayed_assump;
    Int delayed_assump_sum = 0;
    BitMap top_impl_gen(true);
    vec<Int> top_UB_stack;
    bool optimum_found = false;
    Lit last_unsat_constraint_lit = lit_Undef;

    Int LB_goalval = 0, UB_goalval = 0;    
    sort(&soft_cls[0], soft_cls.size(), LT<Pair<weight_t, Minisat::vec<Lit>*> >());
    int j = 0; Lit pj;
    for (int i = 0; i < soft_cls.size(); ++i) {
        soft_cls[i].fst /= goal_gcd;
        if (soft_cls[i].fst < 0) { 
            fixed_goalval += soft_cls[i].fst; soft_cls[i].fst = -soft_cls[i].fst; soft_cls[i].snd->last() = ~soft_cls[i].snd->last(); 
        }
        Lit p = soft_cls[i].snd->last();
        if (soft_cls[i].snd->size() == 1) p = ~p;
        if (value(p) != l_Undef) {
            if (value(p) == l_True) {
                fixed_goalval += soft_cls[i].fst;
                addUnit(p);
            } else {
                if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd);
                addUnit(~p);
            }
        } else if (j > 0 && p == pj)  
            soft_cls[j-1].fst += soft_cls[i].fst;
        else if (j > 0 && p == ~pj) {
            fixed_goalval += (soft_cls[j-1].fst < soft_cls[i].fst ? soft_cls[j-1].fst : soft_cls[i].fst); 
            soft_cls[j-1].fst -= soft_cls[i].fst;
            if (soft_cls[j-1].fst < 0) soft_cls[j-1].fst = -soft_cls[j-1].fst, soft_cls[j-1].snd->last() = pj, pj = ~pj; 
        } else {
            if (j > 0 && soft_cls[j-1].fst == 0) j--;
            if (j < i) soft_cls[j] = soft_cls[i];
            pj = p; j++;
        }
    }
    if (j < soft_cls.size()) soft_cls.shrink(soft_cls.size() - j);
    top_for_strat = top_for_hard = soft_cls.size();
    sort(soft_cls);
    weighted_instance = (soft_cls.size() > 1 && soft_cls[0].fst != soft_cls.last().fst);
    for (int i = 0; i < soft_cls.size(); i++) {
        Lit p = soft_cls[i].snd->last();
        psCs.push(Pair_new(soft_cls[i].snd->size() == 1 ? p : ~p, i));
        if (weighted_instance) sorted_assump_Cs.push(soft_cls[i].fst);
        UB_goalval += soft_cls[i].fst;
    }
    LB_goalval += fixed_goalval, UB_goalval += fixed_goalval;
    sort(psCs);
    if (weighted_instance) sortUnique(sorted_assump_Cs);
    if (LB_goalvalue < LB_goalval) LB_goalvalue = LB_goalval;
    if (UB_goalvalue == Int_MAX)   UB_goalvalue = UB_goalval;
    else {
        for (int i = 0; i < psCs.size(); i++)
            goal_ps.push(~psCs[i].fst), goal_Cs.push(soft_cls[psCs[i].snd].fst);
        if (try_lessthan == Int_MAX) try_lessthan = ++UB_goalvalue;
        if (goal_ps.size() > 0) {
            addConstr(goal_ps, goal_Cs, try_lessthan - fixed_goalval, -2, assump_lit);
            convertPbs(false);
        }
    }
    if (opt_minimization != 1 || sorted_assump_Cs.size() == 0) {
        for (int i = 0; i < psCs.size(); i++)
            assump_ps.push(psCs[i].fst), assump_Cs.push(Int(soft_cls[psCs[i].snd].fst));
        for (int i = 0; i < soft_cls.size(); i++) { 
            if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd);
        }
        top_for_strat = top_for_hard = 0;
    } else {
        for (int i = soft_cls.size() - 1; i >= 0; i--) 
            for (int j = soft_cls[i].snd->size() - 1; j >= 0; j--) 
                sat_solver.setFrozen(var((*soft_cls[i].snd)[j]), true);
        Int sum = 0;
        int ml_opt = 0;
        vec<weight_t> sortedCs;
        multi_level_opt.push(false); sum_sorted_soft_cls.push(Pair_new(0, true));
        for (int i = 0, cnt = 0, sz = sorted_assump_Cs.size(), j = 1; j < sz; j++) {
            while (i < soft_cls.size() && soft_cls[i].fst < sorted_assump_Cs[j])
                sortedCs.push(soft_cls[i].fst), sum += soft_cls[i++].fst, cnt++;
            sum_sorted_soft_cls.push(Pair_new(sum, sum < sorted_assump_Cs[j]));
            multi_level_opt.push(sum < sorted_assump_Cs[j]);
            if (multi_level_opt.last()) ml_opt++;
        }
        extern void separationIndex(const vec<weight_t>& cs, vec<int>& separation_points);
        vec<int> gbmo_points; // generalized Boolean multilevel optimization points (GBMO)
        separationIndex(sortedCs, gbmo_points); // find GBMO
        for (int i = 0; i < gbmo_points.size(); i++) 
            multi_level_opt[bin_search(sorted_assump_Cs, sortedCs[gbmo_points[i]])] |= 2;
        if (gbmo_points.size() > 0 && opt_verbosity >= 1)
            reportf("Generalized BMO splitting point(s) found and can be used.\n");
        sortedCs.clear(); gbmo_points.clear();

        //opt_stratification(sorted_assump_Cs, sum_sorted_soft_cls);
        opt_lexicographic = (opt_output_top < 0); // true;
        if (opt_verbosity >= 1 && ml_opt > 0 && opt_output_top < 0) 
            reportf("Boolean multilevel optimization (BMO) can be done in %d point(s).%s\n", 
                    ml_opt, (opt_lexicographic ? "" : " Try -lex-opt option."));
        max_assump_Cs = do_stratification(sat_solver, sorted_assump_Cs, soft_cls, top_for_strat, assump_ps, assump_Cs);
    }
    if (psCs.size() > 0) max_assump = psCs.last().fst;
    if (opt_minimization == 1 && opt_maxsat_prepr) 
        preprocess_soft_cls(assump_ps, assump_Cs, max_assump, max_assump_Cs, delayed_assump, delayed_assump_sum);
    if (opt_verbosity >= 1)
        sat_solver.printVarsCls(goal_ps.size() > 0, &soft_cls, top_for_strat);

    if (opt_polarity_sug != 0)
        for (int i = 0; i < soft_cls.size(); i++){
            Lit p = soft_cls[i].snd->last(); if (soft_cls[i].snd->size() == 1) p = ~p;
            bool dir = opt_polarity_sug > 0 ? !sign(p) : sign(p);
            sat_solver.setPolarity(var(p), LBOOL(dir));
        }
    bool first_time = false;
    if (opt_cpu_lim != INT32_MAX) {
        int used_cpu = cpuTime();
        first_time=true; limitTime(used_cpu + (opt_cpu_lim - used_cpu)/4);
    }
    lbool status;
    while (1) {
      if (use_base_assump) for (int i = 0; i < base_assump.size(); i++) assump_ps.push(base_assump[i]);
      if (opt_minimization == 1 && opt_to_bin_search && sat_solver.conflicts < opt_unsat_conflicts)
          sat_solver.setConfBudget(opt_unsat_conflicts - sat_solver.conflicts);
      else sat_solver.budgetOff();
      status = 
          base_assump.size() == 1 && base_assump[0] == assump_lit ? l_True :
          base_assump.size() == 1 && base_assump[0] == ~assump_lit ? l_False :
          sat_solver.solveLimited(assump_ps);
      if (use_base_assump) {
          for (int i = 0; i < base_assump.size(); i++) {
              if (status == l_True && var(base_assump[i]) < pb_n_vars) addUnit(base_assump[i]);
              assump_ps.pop();
          }
          if (status != l_Undef) base_assump.clear();
      }
      if (first_time) { 
        first_time = false; sat_solver.clearInterrupt(); 
        if (asynch_interrupt && cpu_interrupt) asynch_interrupt = false;
        cpu_interrupt = false; limitTime(opt_cpu_lim);
        if (status == l_Undef) continue;
      }
      if (status  == l_Undef) {
        if (asynch_interrupt) { reportf("*** Interrupted ***\n"); break; }
        if (opt_minimization == 1 && opt_to_bin_search && sat_solver.conflicts >= opt_unsat_conflicts) goto SwitchSearchMethod;
      } else if (status == l_True) { // SAT returned
        if (opt_minimization == 1 && opt_delay_init_constraints) {
            opt_delay_init_constraints = false;
            convertPbs(false);
            constrs.clear();
            continue;
        }
        Int lastCs = 1;
        if(opt_minimization != 1 && assump_ps.size() == 1 && assump_ps.last() == assump_lit) {
          addUnit(assump_lit);
          lastCs = assump_Cs.last();
          assump_ps.pop(); assump_Cs.pop(); assump_lit = lit_Undef;
        }
        sat = true;

        if (cmd == sc_AllSolutions){
            Minisat::vec<Lit>    ban;
            n_solutions++;
            reportf("MODEL# %d:", n_solutions);
            for (Var x = 0; x < pb_n_vars; x++){
                assert(sat_solver.modelValue(x) != l_Undef);
                ban.push(mkLit(x, sat_solver.modelValue(x) == l_True));
                if (index2name[x][0] != '#')
                    reportf(" %s%s", (sat_solver.modelValue(x) == l_False)?"-":"", index2name[x]);
            }
            reportf("\n");
            sat_solver.addClause_(ban);
        }else{
            vec<bool> model;
            Minisat::vec<Lit> soft_unsat;
            for (Var x = 0; x < pb_n_vars; x++)
                assert(sat_solver.modelValue(x) != l_Undef),
                model.push(sat_solver.modelValue(x) == l_True);
            for (int i = 0; i < top_for_strat; i++)
                if (soft_cls[i].snd->size() > 1)
                    model[var(soft_cls[i].snd->last())] = !sign(soft_cls[i].snd->last());
            Int goalvalue = evalGoal(soft_cls, model, soft_unsat) + fixed_goalval;
            extern bool opt_satisfiable_out;
            if (goalvalue < best_goalvalue || opt_output_top > 0 && goalvalue == best_goalvalue) {
                best_goalvalue = goalvalue;
                model.moveTo(best_model);
                char* tmp = toString(best_goalvalue * goal_gcd);
                if (opt_satisfiable_out && opt_output_top < 0 && (opt_satlive || opt_verbosity == 0))
                    printf("o %s\n", tmp), fflush(stdout);
                else if (opt_verbosity > 0 || !opt_satisfiable_out) 
                    reportf("%s solution: %s\n", (optimum_found ? "Next" : "Found"), tmp);
                xfree(tmp);
            } else model.clear(); 
            if (best_goalvalue < UB_goalvalue && opt_output_top < 0) UB_goalvalue = best_goalvalue;
            else if (opt_output_top > 1) {
                while (top_UB_stack.size() > 0 && top_UB_stack.last() < best_goalvalue) top_UB_stack.pop();
                if (top_UB_stack.size() == 0 || top_UB_stack.last() > best_goalvalue) top_UB_stack.push(best_goalvalue);
                if (top_UB_stack.size() >= opt_output_top) {
                    Int &bound = top_UB_stack[top_UB_stack.size() - opt_output_top];
                    if (bound < UB_goalvalue) UB_goalvalue = bound;
                }
            }
            if (cmd == sc_FirstSolution || (opt_minimization == 1 || UB_goalvalue == LB_goalvalue) &&
                                           sorted_assump_Cs.size() == 0 && delayed_assump.empty())
                if (opt_minimization == 1 && opt_output_top > 0) {
                    outputResult(*this, false);
                    if (opt_verbosity > 0 && !optimum_found) {
                        optimum_found = true;
                        char* tmp = toString(best_goalvalue * goal_gcd);
                        reportf(" OPT SOLUTION: %s\n", tmp);
                        xfree(tmp);
                    }
                    if (--opt_output_top == 0) break;
                    else { 
                        best_goalvalue = Int_MAX;
                        if (soft_unsat.size() > 0) sat_solver.addClause(soft_unsat);
                        else { status = l_False; break; }
                        for (int i = 0; i < soft_cls.size(); i++)
                            if (soft_unsat[i] == soft_cls[i].snd->last() && soft_cls[i].snd->size() > 1 && 
                                    top_impl_gen.at(var(soft_unsat[i]))) {
                                top_impl_gen.set(var(soft_unsat[i]), false);
                                for (int j = soft_cls[i].snd->size() - 2; j >= 0; j--)
                                    sat_solver.addClause(~soft_unsat[i], ~(*soft_cls[i].snd)[j]);
                            }
                        continue;
                    }
                } else break;
            if (opt_minimization == 1) {
                assert(sorted_assump_Cs.size() > 0 || !delayed_assump.empty()); 
                int old_top = top_for_strat;
                if (delayed_assump.empty() || sorted_assump_Cs.size() > 0 && Int(sorted_assump_Cs.last()) > delayed_assump.top().fst) {
                    if (opt_lexicographic && multi_level_opt[sorted_assump_Cs.size()]) {
                        bool standard_multi_level_opt = multi_level_opt[sorted_assump_Cs.size()] & 1;
                        bool general_multi_level_opt = multi_level_opt[sorted_assump_Cs.size()] & 2;
                        Int bound = sum_sorted_soft_cls[sorted_assump_Cs.size()].fst + delayed_assump_sum;
                        int cnt_assump = 0;
                        if (general_multi_level_opt && assump_ps.last() == last_unsat_constraint_lit)
                            addUnit(assump_ps.last()), assump_Cs.last() = -assump_Cs.last(), cnt_assump++;
                        if (standard_multi_level_opt)
                            for (int i = 0; i < assump_ps.size() && assump_ps[i] <= max_assump; i++)
                                if (assump_Cs[i] > bound)
                                    addUnit(assump_ps[i]), assump_Cs[i] = -assump_Cs[i], cnt_assump++;
                        if (cnt_assump > 0) {
                            clear_assumptions(assump_ps, assump_Cs);
                            if (opt_verbosity > 0) reportf("BMO - done.\n");
                        }
                    }
                    max_assump_Cs = do_stratification(sat_solver, sorted_assump_Cs, soft_cls, top_for_strat, assump_ps, assump_Cs);
                } else {
                    max_assump_Cs = delayed_assump.top().fst;
                    vec<Pair<Lit, Int> > new_assump;
                    do { 
                        new_assump.push(Pair_new(delayed_assump.top().snd, max_assump_Cs));
                        delayed_assump_sum -= delayed_assump.top().fst;
                        delayed_assump.pop(); 
                    } while (!delayed_assump.empty() && delayed_assump.top().fst >= max_assump_Cs);
                    sort(new_assump); int sz = new_assump.size();
                    assump_ps.growTo(assump_ps.size() + sz); assump_Cs.growTo(assump_Cs.size() + sz);
                    for (int i = assump_ps.size() - 1; i >= sz; i--)
                        assump_ps[i] = assump_ps[i-sz], assump_Cs[i] = assump_Cs[i-sz];
                    for (int fr = sz, to = 0, i = 0; i < new_assump.size(); i++) {
                        Lit p = new_assump[i].fst;
                        while (fr < assump_ps.size() && assump_ps[fr] <= p)
                            assump_ps[to] = assump_ps[fr], assump_Cs[to++] = assump_Cs[fr++];
                        assump_ps[to] = p; assump_Cs[to++] = new_assump[i].snd;
                    }
                }
                harden_soft_cls(assump_ps, assump_Cs);
                if (top_for_strat < old_top) {
                    try_lessthan = best_goalvalue;
                    if (opt_maxsat_prepr) 
                        preprocess_soft_cls(assump_ps, assump_Cs, max_assump, max_assump_Cs, delayed_assump, delayed_assump_sum);
                }
                continue;
            } else harden_soft_cls(assump_ps, assump_Cs);
            if (opt_minimization == 0 || best_goalvalue - LB_goalvalue < opt_seq_thres) {
                opt_minimization = 0;
                assump_lit = (assump_ps.size() == 0 ? lit_Undef : mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true));
                try_lessthan = best_goalvalue;
            } else {
                assump_lit = assump_lit == lit_Undef || !use_base_assump ?
                    mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars)) : assump_lit;
                try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;
            }
            Int goal_diff = harden_goalval+fixed_goalval;
            if (!addConstr(goal_ps, goal_Cs, try_lessthan - goal_diff, -2, assump_lit))
                break; // unsat
            if (assump_lit != lit_Undef && !use_base_assump) {
                sat_solver.setFrozen(var(assump_lit),true);
                assump_ps.push(assump_lit), assump_Cs.push(opt_minimization == 2 ? try_lessthan : lastCs);
            }
            last_unsat_constraint_lit = lit_Undef;
            convertPbs(false);
        }
      } else { // UNSAT returned
        if (assump_ps.size() == 0 && assump_lit == lit_Undef || 
            opt_minimization == 0 && sat_solver.conflict.size() == 1 && sat_solver.conflict[0] == ~assump_lit) break;
        {
        Minisat::vec<Lit> core_mus;
        if (opt_core_minimization) {
            if (weighted_instance) {
                vec<Pair<Pair<Int, int>, Lit> > Cs_mus;
                for (int i = 0; i < sat_solver.conflict.size(); i++) {
                    Lit p = ~sat_solver.conflict[i];
                    int j = bin_search(assump_ps, p);
                    Cs_mus.push(Pair_new(Pair_new((j>=0 ? assump_Cs[j] : 0),i),p));
                }
                sort(Cs_mus);
                for (int i = 0; i < Cs_mus.size(); i++) core_mus.push(Cs_mus[i].snd);
            } else
                for (int i = 0; i < sat_solver.conflict.size(); i++) core_mus.push(~sat_solver.conflict[i]);
            core_minimization(sat_solver, core_mus);
        } else
            for (int i = 0; i < sat_solver.conflict.size(); i++) core_mus.push(sat_solver.conflict[i]);
        if (core_mus.size() > 0 && core_mus.size() < 6) sat_solver.addClause(core_mus);
        Int min_removed = Int_MAX, min_bound = Int_MAX;
        int removed = 0;
        bool other_conflict = false;

        if (opt_minimization == 1) { 
            goal_ps.clear(); goal_Cs.clear();
        }
        for (int j, i = 0; i < core_mus.size(); i++) {
            Lit p = ~core_mus[i];
            if ((j = bin_search(assump_ps, p)) >= 0) { 
                if (opt_minimization == 1 || p <= max_assump) {
                    goal_ps.push(~p), goal_Cs.push(opt_minimization == 1 ? 1 : assump_Cs[j]);
                    if (assump_Cs[j] < min_removed) min_removed = assump_Cs[j];
                } else { 
                    other_conflict = true;
                    if (assump_Cs[j] < min_bound) min_bound = assump_Cs[j];
                }
                assump_Cs[j] = -assump_Cs[j]; removed++;
            }
        }
        if (other_conflict && min_removed != Int_MAX && opt_minimization != 1) min_removed = 0;
        vec<int> modified_saved_constrs;
        if (removed > 0) {
            int j = 0;
            for (int i = 0; i < assump_ps.size(); i++) {
                if (assump_Cs[i] < 0) {
                    Minisat::Lit p = assump_ps[i];
                    if (opt_minimization == 1 && p > max_assump) { // && assump_Cs[i] == -min_removed) {
                        int k = assump_map.at(toInt(p));
                        if (k >= 0 && k < saved_constrs.size() &&  saved_constrs[k] != NULL && saved_constrs[k]->lit == p) {
                            if (saved_constrs[k]->lo != Int_MIN && saved_constrs[k]->lo > 1 || 
                                    saved_constrs[k]->hi != Int_MAX && saved_constrs[k]->hi < saved_constrs[k]->size - 1) {
                                if (saved_constrs[k]->lo != Int_MIN) --saved_constrs[k]->lo; else ++saved_constrs[k]->hi;
                                constrs.push(saved_constrs[k]); 
                                constrs.last()->lit = lit_Undef;
                                modified_saved_constrs.push(k);
                            } else { saved_constrs[k]->~Linear(); saved_constrs[k] = NULL; }
                            assump_map.set(toInt(p), -1);
                        }
                    }
                    if (assump_Cs[i] == -min_removed || opt_minimization != 1) continue;
                    assump_Cs[i] = -min_removed - assump_Cs[i];
                    if (opt_minimization == 1 &&  assump_Cs[i] < max_assump_Cs ) {
                        delayed_assump.push(Pair_new(assump_Cs[i], assump_ps[i]));
                        delayed_assump_sum += assump_Cs[i];
                        continue;
                    }
                }
                if (j < i) assump_ps[j] = assump_ps[i], assump_Cs[j] = assump_Cs[i];
                j++;
            }
            if ((removed = assump_ps.size() - j) > 0)
                assump_ps.shrink(removed), assump_Cs.shrink(removed);
            if (min_bound == Int_MAX || min_bound < LB_goalvalue) min_bound = LB_goalvalue + 1;
            LB_goalvalue = (min_removed == 0 ? next_sum(LB_goalvalue - fixed_goalval - harden_goalval, goal_Cs) + fixed_goalval + harden_goalval: 
                            min_removed == Int_MAX ? min_bound : LB_goalvalue + min_removed);
        } else if (opt_minimization == 1) LB_goalvalue = next_sum(LB_goalvalue - fixed_goalval - harden_goalval, goal_Cs) + fixed_goalval + harden_goalval; 
        else LB_goalvalue = try_lessthan;

        if (LB_goalvalue == best_goalvalue && opt_minimization != 1) break;

        Int goal_diff = harden_goalval+fixed_goalval;
        if (opt_minimization == 1) {
            assump_lit = lit_Undef;
            try_lessthan = goal_diff + 2;
	} else if (opt_minimization == 0 || best_goalvalue == Int_MAX || best_goalvalue - LB_goalvalue < opt_seq_thres) {
            if (best_goalvalue != Int_MAX) opt_minimization = 0;
            assump_lit = (assump_ps.size() == 0 ? lit_Undef : mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true));
	    try_lessthan = (best_goalvalue != Int_MAX ? best_goalvalue : UB_goalvalue+1);
	} else {
            assump_lit = assump_lit == lit_Undef || !use_base_assump ?
                mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars)) : assump_lit;
	    try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;
	}
        if (!addConstr(goal_ps, goal_Cs, try_lessthan - goal_diff, -2, assump_lit))
            break; // unsat
        if (constrs.size() > 0 && (opt_minimization != 1 || !opt_delay_init_constraints)) {
            convertPbs(false);
            if (opt_minimization == 1) {
                if (constrs.size() == modified_saved_constrs.size() + 1) assump_lit = constrs.last()->lit;
                for (int i = 0, j = 0; i < modified_saved_constrs.size(); i++) {
                    int k = modified_saved_constrs[i];
                    Lit newp = constrs[j++]->lit;
                    sat_solver.setFrozen(var(newp),true);
                    sat_solver.addClause(~saved_constrs[k]->lit, newp);
                    saved_constrs[k]->lit = newp;
                    assump_ps.push(newp); assump_Cs.push(saved_constrs_Cs[k]);
                    if (saved_constrs[k]->lo > 1 || saved_constrs[k]->hi < saved_constrs[k]->size - 1)
                        assump_map.set(toInt(newp), k);
                }
                modified_saved_constrs.clear();
            }
        }
        if (assump_lit != lit_Undef && !use_base_assump) {
            sat_solver.setFrozen(var(assump_lit),true);
            assump_ps.push(assump_lit); assump_Cs.push(opt_minimization == 2 ? try_lessthan : 
                                                       min_removed != Int_MAX && min_removed != 0 ? min_removed : 1);
        }
        last_unsat_constraint_lit = lit_Undef;
        if (opt_minimization == 1) {
            last_unsat_constraint_lit = assump_lit;
            if (constrs.size() > 0 && constrs.last()->lit == assump_lit) {
                Minisat::vec<Lit> new_assump; 
                optimize_last_constraint(constrs, assump_ps, new_assump);
                if (new_assump.size() > 0) {
                    delayed_assump_sum += Int(new_assump.size()) * assump_Cs.last();
                    for (int i=0; i < new_assump.size(); i++) 
                        delayed_assump.push(Pair_new(assump_Cs.last(), new_assump[i]));
                }
                if (constrs.last()->lit != assump_lit) assump_lit = assump_ps.last() = constrs.last()->lit;
                saved_constrs.push(constrs.last()), assump_map.set(toInt(assump_lit),saved_constrs.size() - 1);
                saved_constrs_Cs.push(assump_Cs.last());
            } else if (goal_ps.size() > 1) {
                saved_constrs.push(new (mem.alloc(sizeof(Linear) + goal_ps.size()*(sizeof(Lit) + sizeof(Int))))
                        Linear(goal_ps, goal_Cs, Int_MIN, 1, assump_lit));
                assump_map.set(toInt(assump_lit),saved_constrs.size() - 1);
                saved_constrs_Cs.push(assump_Cs.last());
            }
            if (!opt_delay_init_constraints) {
                int j = 0;
                for (int i = 0; i < saved_constrs.size(); i++)
                    if (saved_constrs[i] != NULL) {
                        if (saved_constrs[i]->lo == 1 && saved_constrs[i]->hi == Int_MAX || 
                                saved_constrs[i]->hi == saved_constrs[i]->size - 1 && saved_constrs[i]->lo == Int_MIN ) {
                            saved_constrs[i]->~Linear();
                            saved_constrs[i] = NULL;
                        } else {
                            if (j < i) {
                                saved_constrs[j] = saved_constrs[i],  saved_constrs[i] = NULL, saved_constrs_Cs[j] = saved_constrs_Cs[i];
                                if (saved_constrs[j]->lit != lit_Undef) assump_map.set(toInt(saved_constrs[j]->lit), j); 
                            }
                            j++;
                        }
                    }
                if (j < saved_constrs.size()) 
                    saved_constrs.shrink(saved_constrs.size() - j), saved_constrs_Cs.shrink(saved_constrs_Cs.size() - j);
                constrs.clear();
            }
        }
        }
        if (weighted_instance && sat && sat_solver.conflicts > 10000)
            harden_soft_cls(assump_ps, assump_Cs);
        if (opt_minimization >= 1 && opt_verbosity >= 2) {
            char *t; reportf("Lower bound  = %s, assump. size = %d, stratif. level = %d (cls: %d, wght: %s)\n", t=toString(LB_goalvalue * goal_gcd), 
                    assump_ps.size(), sorted_assump_Cs.size(), top_for_strat, toString(sorted_assump_Cs.size() > 0 ? sorted_assump_Cs.last() : 0)); xfree(t); }
        if (opt_minimization == 2 && opt_verbosity == 1 && use_base_assump) {
            char *t; reportf("Lower bound  = %s\n", t=toString(LB_goalvalue * goal_gcd)); xfree(t); }
SwitchSearchMethod:        
        if (opt_minimization == 1 && opt_to_bin_search && LB_goalvalue + 5 < UB_goalvalue &&
                cpuTime() >= opt_unsat_cpu && sat_solver.conflicts > opt_unsat_conflicts) {
            int cnt = 0;
            for (int j = 0, i = 0; i < psCs.size(); i++) {
                const Int &w = soft_cls[psCs[i].snd].fst;
                if (j == assump_ps.size() || psCs[i].fst < assump_ps[j] || psCs[i].fst == assump_ps[j] && w > assump_Cs[j])
                    if (++cnt >= 50000) { opt_to_bin_search = false; break; }
                if (j < assump_ps.size() && psCs[i].fst == assump_ps[j]) j++;
            }
            if (opt_to_bin_search) {
                for (int i = assump_ps.size() - 1; i >= 0 && assump_ps[i] > max_assump; i--)
                    assump_ps.pop(), assump_Cs.pop();
                goal_ps.clear(); goal_Cs.clear();
                bool clear_assump = (cnt * 3 >= assump_ps.size()); use_base_assump = clear_assump;
                Int sumCs(0);
                int k = 0;
                for (int j = 0, i = 0; i < psCs.size(); i++) {
                    const Int &w = soft_cls[psCs[i].snd].fst;
                    bool in_harden = harden_lits.has(psCs[i].fst);
                    if ((j == assump_ps.size() || psCs[i].fst < assump_ps[j] || 
                            psCs[i].fst == assump_ps[j] && (clear_assump || w > assump_Cs[j] || in_harden)) &&
                        (!in_harden || harden_lits.at(psCs[i].fst) < w))
                            goal_ps.push(~psCs[i].fst), goal_Cs.push(in_harden ? w - harden_lits.at(psCs[i].fst) : w), 
                                sumCs += goal_Cs.last();
                    if (j < assump_ps.size() && psCs[i].fst == assump_ps[j]) {
                        if (!clear_assump && w == assump_Cs[j] && !in_harden) { 
                            if (k < j) assump_ps[k] = assump_ps[j], assump_Cs[k] = assump_Cs[j];
                            k++;
                        }
                        j++;
                    }
                }      
                if (k < assump_ps.size()) assump_ps.shrink(assump_ps.size() - k), assump_Cs.shrink(assump_Cs.size() - k);
                for (int i = 0; i < top_for_strat; i++) { 
                    if (soft_cls[i].snd->size() > 1) sat_solver.addClause(*soft_cls[i].snd);
                }
                for (int i = 0; i < am1_rels.size(); i++) 
                    goal_ps.push(~am1_rels[i].fst), goal_Cs.push(am1_rels[i].snd), sumCs += goal_Cs.last();
                {   Int lower_bound = LB_goalvalue-fixed_goalval-harden_goalval; int j = 0;
                    for (int i = 0; i < goal_Cs.size(); i++)
                        if (sumCs - goal_Cs[i] < lower_bound) addUnit(goal_ps[i]), fixed_goalval += goal_Cs[i];
                        else { if (j < i) goal_ps[j] = goal_ps[i], goal_Cs[j] = goal_Cs[i]; j++; }
                    if (j < goal_ps.size()) goal_ps.shrink(goal_ps.size() - j), goal_Cs.shrink(goal_Cs.size() - j);
                }
                top_for_strat = 0; sorted_assump_Cs.clear(); am1_rels.clear(); harden_lits.clear();
                delayed_assump.clear(); delayed_assump_sum = 0;
                if (opt_verbosity >= 1) {
                    reportf("Switching to binary search ... (after %g s and %d conflicts) with %d goal literals and %d assumptions\n", 
                            cpuTime(), sat_solver.conflicts, goal_ps.size(), assump_ps.size());
                }
                opt_minimization = 2;
                if (opt_convert_goal != ct_Undef) opt_convert = opt_convert_goal;
                if (sat) {
                    try_lessthan = best_goalvalue; 
                    assump_lit = (assump_ps.size() == 0 && !use_base_assump ? lit_Undef : 
                                                          mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true));
                    if (assump_lit != lit_Undef && !use_base_assump) assump_ps.push(assump_lit), assump_Cs.push(try_lessthan);
                    if (!addConstr(goal_ps, goal_Cs, try_lessthan - fixed_goalval - harden_goalval, -2, assump_lit))
                        break; // unsat
                    if (constrs.size() > 0) convertPbs(false);
                }
            }
        }
      }         
    } // END OF LOOP

    if (status == l_False && opt_output_top > 0) printf("v\n");
    if (goal_gcd != 1) {
        if (best_goalvalue != Int_MAX) best_goalvalue *= goal_gcd;
        if (LB_goalvalue   != Int_MIN) LB_goalvalue *= goal_gcd;
        if (UB_goalvalue   != Int_MAX) UB_goalvalue *= goal_gcd;
    }
    if (opt_verbosity >= 1 && opt_output_top < 0){
        if      (!sat)
            reportf(asynch_interrupt ? "\bUNKNOWN\b\n" : "\bUNSATISFIABLE\b\n");
        else if (soft_cls.size() == 0 && best_goalvalue == INT_MAX)
            reportf("\bSATISFIABLE: No goal function specified.\b\n");
        else if (cmd == sc_FirstSolution){
            char* tmp = toString(best_goalvalue);
            reportf("\bFirst solution found: %s\b\n", tmp);
            xfree(tmp);
        }else if (asynch_interrupt){
            extern bool opt_use_maxpre;
            char* tmp = toString(best_goalvalue);
            if (!opt_use_maxpre) reportf("\bSATISFIABLE: Best solution found: %s\b\n", tmp);
            xfree(tmp);
       }else{
            char* tmp = toString(best_goalvalue);
            reportf("\bOptimal solution: %s\b\n", tmp);
            xfree(tmp);
        }
    }
}

int lower_bound(vec<Lit>& set, Lit elem)
{
    int count = set.size(), fst = 0, step, it;
    while (count > 0) {
        step = count / 2; it = fst + step;
        if (set[it] < elem) fst = ++it, count -= step + 1;
        else count = step;
    }
    return fst;
}

void set_difference(vec<Lit>& set1, const vec<Lit>& set2)
{
    int j, k = 0, n1 = set1.size(), n2 = set2.size();
    if (n2 == 0) return;
    if (n2 == 1) {
        j = n1;
        if ((k=bin_search(set1, set2[0])) >= 0)
            memmove(&set1[k], &set1[k+1], sizeof(Lit)*(n1 - k - 1)), j--;
    } else {
        Lit *it2 = (Lit *)&set2[0], *fin2 = it2 + n2;
        Lit *ok1 = (Lit *)&set1[0] + lower_bound(set1, *it2);
        Lit *it1 = ok1, *fwd = ok1, *fin1 = (Lit *)&set1[0] + n1;
        while (fwd < fin1) {
            while (it2 < fin2 && *it2 < *fwd) it2++;
            if (it2 < fin2) {
                while (fwd < fin1 && *fwd < *it2) fwd++;
                if (fwd >= fin1 || *fwd == *it2) {
                    if (ok1 < it1) memmove(ok1, it1, sizeof(Lit)*(fwd - it1));
                    ok1 += fwd - it1; it1 = ++fwd; it2++;
                } 
            } else { 
                if (ok1 < it1) memmove(ok1, it1, sizeof(Lit)*(fin1 - it1)); 
                ok1 += fin1 - it1; break; 
            }
        }
        j = ok1 - &set1[0];
    }
    if (j < n1) set1.shrink(n1 - j);
}

struct mapLT { Map<Lit, vec<Lit>* >&c; bool operator()(Lit p, Lit q) { return c.at(p)->size() < c.at(q)->size(); }};

void MsSolver::preprocess_soft_cls(Minisat::vec<Lit>& assump_ps, vec<Int>& assump_Cs, const Lit max_assump, const Int& max_assump_Cs, 
                                              IntLitQueue& delayed_assump, Int& delayed_assump_sum)
{
    Map<Lit, vec<Lit>* > conns;
    vec<Lit> conns_lit;
    vec<Lit> confl;
    vec<Lit> lits;
    for (int i = 0; i < assump_ps.size() && assump_ps[i] <= max_assump; i++) {
        Minisat::vec<Lit> props;
        Lit assump = assump_ps[i];
        if (sat_solver.prop_check(assump, props))
            for (int l, j = 0; j < props.size(); j++) {
                if ((l = bin_search(assump_ps,  ~props[j])) >= 0 && assump_ps[l] <= max_assump) {
                    if (!conns.has(assump)) conns.set(assump,new vec<Lit>());
                    conns.ref(assump)->push(~props[j]);
                    if (!conns.has(~props[j])) conns.set(~props[j], new vec<Lit>());
                    conns.ref(~props[j])->push(assump);
                }
            }  
        else confl.push(assump);
    }
    conns.domain(conns_lit);
    if (confl.size() > 0) {
        for (int i = 0; i < conns_lit.size(); i++) {
            if (bin_search(confl, conns_lit[i]) >= 0) {
                delete conns.ref(conns_lit[i]);
                conns.exclude(conns_lit[i]);
            } else {
                vec<Lit>& dep_lit = *conns.ref(conns_lit[i]);
                sortUnique(dep_lit);
                set_difference(dep_lit, confl);
                if (dep_lit.size() == 0) { delete conns.ref(conns_lit[i]); conns.exclude(conns_lit[i]); }
                else lits.push(conns_lit[i]);
            }
        }
        conns_lit.clear(); conns.domain(conns_lit);
        for (int l, i = 0; i < confl.size(); i++) {
            Lit p = confl[i];
            if ((l = bin_search(assump_ps, p)) >= 0 && assump_ps[l] <= max_assump) {
                if (!harden_lits.has(p)) harden_lits.set(p, assump_Cs[l]); else harden_lits.ref(p) += assump_Cs[l];
                harden_goalval += assump_Cs[l];
                addUnit(~p); LB_goalvalue += assump_Cs[l]; assump_Cs[l] = -assump_Cs[l];
            }
        }
        if (opt_verbosity >= 2) reportf("Found %d Unit cores\n", confl.size());
    } else
        for (int i = 0; i < conns_lit.size(); i++) { 
            lits.push(conns_lit[i]); 
            sortUnique(*conns.ref(conns_lit[i])); 
        }
    sort(lits);
    mapLT cmp {conns};
    int am1_cnt = 0, am1_len_sum = 0;
    //for (int i = 100000; i > 0 && lits.size() > 0; i--) {
    while (lits.size() > 0) {
        vec<Lit> am1;
        Lit minl = lits[0];
        for (int new_sz,  sz = conns.at(minl)->size(), i = 1; i < lits.size(); i++)
            if ((new_sz = conns.at(lits[i])->size()) < sz) minl = lits[i], sz = new_sz;
        am1.push(minl);
        vec<Lit>& dep_minl = *conns.ref(minl);
        sort(dep_minl, cmp);
        for (int sz = dep_minl.size(), i = 0; i < sz; i++) {
            Lit l = dep_minl[i];
            if (bin_search(lits, l) >= 0) {
                int i;
                const vec<Lit>& dep_l = *conns.at(l);
                for (i = 1; i < am1.size() && bin_search(dep_l, am1[i]) >= 0; ++i);
                if (i == am1.size()) am1.push(l);
            }
        }
        sort(dep_minl);
        sort(am1);
        set_difference(lits, am1);
        for (int i = 0; i < conns_lit.size(); i++)  set_difference(*conns.ref(conns_lit[i]), am1);
        if (am1.size() > 1) {
            Minisat::vec<Lit> cls;
            vec<int> ind;
            Int min_Cs = Int_MAX;
            for (int l, i = 0; i < am1.size(); i++)
                if ((l = bin_search(assump_ps, am1[i])) >= 0 && assump_Cs[l] > 0) {
                    ind.push(l);
                    if (assump_Cs[l] < min_Cs) min_Cs = assump_Cs[l];
                }
                else reportf("am1: %d %d %d %s\n", i, am1.size(), toInt(am1[0]), toInt(am1[i]), (l>=0 && l <assump_Cs.size()?toString(assump_Cs[l]):"???"));
            if (ind.size() < 2) continue;
            for (int i = 0; i < ind.size(); i++) {
                if (assump_Cs[ind[i]] == min_Cs) cls.push(assump_ps[ind[i]]), assump_Cs[ind[i]] = -assump_Cs[ind[i]];
                else {
                    cls.push(assump_ps[ind[i]]); //~r);
                    assump_Cs[ind[i]] -= min_Cs;
                    if (assump_Cs[ind[i]] < max_assump_Cs) {
                        delayed_assump.push(Pair_new(assump_Cs[ind[i]], assump_ps[ind[i]]));
                        delayed_assump_sum += assump_Cs[ind[i]];
                        assump_Cs[ind[i]] = - assump_Cs[ind[i]];
                    }
                }
                if (!harden_lits.has(assump_ps[ind[i]])) harden_lits.set(assump_ps[ind[i]], min_Cs);
                else harden_lits.ref(assump_ps[ind[i]]) += min_Cs;
            }
            Lit r = mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars), true);
            sat_solver.setFrozen(var(r), true);
            cls.push(~r); assump_ps.push(r); assump_Cs.push(min_Cs);
            am1_rels.push(Pair_new(r,min_Cs));
            sat_solver.addClause(cls);
            if (ind.size() > 2) min_Cs = Int(ind.size() - 1) * min_Cs;
            am1_cnt++; am1_len_sum += am1.size();  LB_goalvalue += min_Cs; harden_goalval += min_Cs;
        }
    }
    if (am1_cnt > 0 || confl.size() > 0) clear_assumptions(assump_ps, assump_Cs);
    if (opt_verbosity >= 2 && am1_cnt > 0) 
        reportf("Found %d AtMostOne cores of avg size: %.2f\n", am1_cnt, (double)am1_len_sum/am1_cnt);
}

