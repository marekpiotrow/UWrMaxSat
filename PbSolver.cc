/*************************************************************************************[PbSolver.cc]
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

#include <unistd.h>
#include <signal.h>
#include "System.h"
#include "Sort.h"
#include "Debug.h"

extern int verbosity;


//=================================================================================================
// Interface required by parser:


int PbSolver::getVar(cchar* name)
{
    int ret;
    if (!name2index.peek(name, ret)){
        // Create new variable:
        Var x = index2name.size();
        index2name.push(xstrdup(name));
        n_occurs  .push(0);
        n_occurs  .push(0);
        //assigns   .push(toInt(l_Undef));
        sat_solver.newVar();        // (reserve one SAT variable for each PB variable)
        ret = name2index.set(index2name.last(), x);
    }
    return ret;
}


void PbSolver::allocConstrs(int n_vars, int n_constrs)
{
    declared_n_vars    = n_vars;
    declared_n_constrs = n_constrs;
}


void PbSolver::addGoal(const vec<Lit>& ps, const vec<Int>& Cs)
{
    /**/debug_names = &index2name;
    //**/reportf("MIN: "); dump(ps, Cs); reportf("\n");

    goal = new (xmalloc<char>(sizeof(Linear) + ps.size()*(sizeof(Lit) + sizeof(Int)))) Linear(ps, Cs, Int_MIN, Int_MAX, lit_Undef);
}

bool PbSolver::addConstr(const vec<Lit>& ps, const vec<Int>& Cs, Int rhs, int ineq, Lit& lit) {
  vec<Lit>    norm_ps;
  vec<Int>    norm_Cs;
  Int         norm_rhs;

  #define Copy    do{ norm_ps.clear(); norm_Cs.clear(); for (int i = 0; i < ps.size(); i++) norm_ps.push(ps[i]), norm_Cs.push( Cs[i]); norm_rhs =  rhs; }while(0)
  #define CopyInv do{ norm_ps.clear(); norm_Cs.clear(); for (int i = 0; i < ps.size(); i++) norm_ps.push(ps[i]), norm_Cs.push(-Cs[i]); norm_rhs = -rhs; }while(0)

  // non-normalize ORIGINAL
  if (ineq == 0){

    Copy;
    if (normalizePb(norm_ps, norm_Cs, norm_rhs, lit))
      storePb(norm_ps, norm_Cs, norm_rhs, Int_MAX, lit);

    CopyInv;
    if (normalizePb(norm_ps, norm_Cs, norm_rhs, lit))
      storePb(norm_ps, norm_Cs, norm_rhs, Int_MAX, lit);
  }else{
    if (ineq > 0)
      Copy;
    else {
      CopyInv;
      ineq = -ineq;
    }
    if (ineq == 2)
      ++norm_rhs;

    if (normalizePb(norm_ps, norm_Cs, norm_rhs, lit))
      storePb(norm_ps, norm_Cs, norm_rhs, Int_MAX, lit);
  }
  return okay();
}

//=================================================================================================


static Int gcd(Int small, Int big) {
    return (small == 0) ? big: gcd(big % small, small); }

// Normalize a PB constraint to only positive constants. Depends on:
//
//   bool    ok            -- Will be set to FALSE if constraint is unsatisfiable.
//   lbool   value(Lit)    -- Returns the value of a literal (however, it is sound to always return 'l_Undef', but produces less efficient results)
//   bool    addUnit(Lit)  -- Enqueue unit fact for propagation (returns FALSE if conflict detected).
//
// The two vectors 'ps' and 'Cs' (which are modififed by this method) should be interpreted as:
//
//   'p[0]*C[0] + p[1]*C[1] + ... + p[N-1]*C[N-1] >= C[N]'
//
// The method returns TRUE if constraint was normalized, FALSE if the constraint was already
// satisfied or determined contradictory. The vectors 'ps' and 'Cs' should ONLY be used if
// TRUE is returned.
//

bool PbSolver::normalizePb(vec<Lit>& ps, vec<Int>& Cs, Int& C, Lit& lit)
{
    assert(ps.size() == Cs.size());
    if (!okay()) return false;

    // Remove assigned literals and literals with zero coefficients:
    int new_sz = 0;
    for (int i = 0; i < ps.size(); i++){
        if (value(ps[i]) != l_Undef){
            if (value(ps[i]) == l_True)
                C -= Cs[i];
        }else if (Cs[i] != 0){
            ps[new_sz] = ps[i];
            Cs[new_sz] = Cs[i];
            new_sz++;
        }
    }
    ps.shrink(ps.size() - new_sz);
    Cs.shrink(Cs.size() - new_sz);

    // Group all x/~x pairs
    //
    Map<Var, Pair<Int,Int> >    var2consts(Pair_new(0,0));     // Variable -> negative/positive polarity constant
    for (int i = 0; i < ps.size(); i++){
        Var             x      = var(ps[i]);
        Pair<Int,Int>   consts = var2consts.at(x);
        if (sign(ps[i]))
            consts.fst += Cs[i];
        else
            consts.snd += Cs[i];
        var2consts.set(x, consts);
    }

    // Normalize constants to positive values only:
    //
    vec<Pair<Var, Pair<Int,Int> > > all;
    var2consts.pairs(all);
    vec<Pair<Int,Lit> > Csps(all.size());
    for (int i = 0; i < all.size(); i++){
        if (all[i].snd.fst < all[i].snd.snd){
            // Negative polarity will vanish
            C -= all[i].snd.fst;
            Csps[i] = Pair_new(all[i].snd.snd - all[i].snd.fst, mkLit(all[i].fst));
        }else{
            // Positive polarity will vanish
            C -= all[i].snd.snd;
            Csps[i] = Pair_new(all[i].snd.fst - all[i].snd.snd, ~mkLit(all[i].fst));
        }
    }

    // Sort literals on growing constant values:
    //
    Sort::sort(Csps);     // (use lexicographical order of 'Pair's here)
    Int     sum = 0;
    for (int i = 0; i < Csps.size(); i++){
        Cs[i] = Csps[i].fst, ps[i] = Csps[i].snd, sum += Cs[i];
        if (sum < 0) fprintf(stderr, "ERROR! Too large constants encountered in constraint.\n"), exit(1);
    }
    ps.shrink(ps.size() - Csps.size());
    Cs.shrink(Cs.size() - Csps.size());

    if (opt_maxsat_msu && opt_minimization == 1 && lit == lit_Undef && C >= sum && C != 0) {
        lit = mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars));
        sat_solver.setFrozen(var(lit), true);
    }
    // Propagate already present consequences:
    //
    bool changed;
    do{
        changed = false;
        while (ps.size() > 0 && sum-Cs.last() < C){
            changed = true;
            if (lit != lit_Undef) {
                if (use_base_assump) base_assump.push(ps.last());
                else {
                    vec<Lit> ban;
                    ban.push( ~lit );
                    ban.push(ps.last());
                    addClause(ban);
                }
            } else if (!addUnit(ps.last())) {
              sat_solver.addEmptyClause();
              return false;
            }
            sum -= Cs.last();
            C   -= Cs.last();
            ps.pop(); Cs.pop();
        }

        // Trivially true or false?
        if (C <= 0) {
            if (lit != lit_Undef && use_base_assump && base_assump.size() == 0) base_assump.push(lit);
            return false;
        }
        if (sum < C) {
            if (lit != lit_Undef) {
                if (use_base_assump) { base_assump.clear(); base_assump.push(~lit); } else addUnit(~lit);
            } else sat_solver.addEmptyClause();
            return false;
        }
        assert(sum - Cs[ps.size()-1] >= C);

        // GCD:
        assert(Cs.size() > 0);
        Int     div = Cs[0];
        for (int i = 1; i < Cs.size() && div != 1; i++)
            div = gcd(div, Cs[i]);
        if (div != 1) {
            for (int i = 0; i < Cs.size(); i++)
                Cs[i] /= div;
            sum /= div;
            C = (C + div-1) / div;
            changed = true;
        }
        // Trim constants:
        for (int i = Cs.size() - 1; i >= 0; i--)
            if (Cs[i] > C)
                changed = true,
                sum -= Cs[i]-C,
                Cs[i] = C;
            else break;
    }while (changed);

    return true;
}

void PbSolver::storePb(const vec<Lit>& ps, const vec<Int>& Cs, Int lo, Int hi, Lit lit)
{
    assert(ps.size() == Cs.size());
    for (int i = 0; i < ps.size(); i++)
        if (toInt(ps[i]) < n_occurs.size()) n_occurs[toInt(ps[i])]++;

    if (lit!=lit_Undef && n_occurs.size() > toInt(lit))
        n_occurs[toInt(lit)]++;

    constrs.push(new (mem.alloc(sizeof(Linear) + ps.size()*(sizeof(Lit) + sizeof(Int)))) Linear(ps, Cs, lo, hi, lit));
}

//=================================================================================================


// Returns TRUE if the constraint should be deleted. May set the 'ok' flag to false
bool PbSolver::propagate(Linear& c)
{
    //**/reportf("BEFORE propagate()\n");
    //**/dump(c, sat_solver.assigns_ref()); reportf("\n");

    // Remove assigned literals:
    Int     sum = 0, true_sum = 0;
    int     j = 0;
    for (int i = 0; i < c.size; i++){
        assert(c(i) > 0);
        if (value(c[i]) == l_Undef){
            sum += c(i);
            c(j) = c(i);
            c[j] = c[i];
            j++;
        }else if (value(c[i]) == l_True)
            true_sum += c(i);
    }
    c.size = j;
    if (c.lo != Int_MIN) c.lo -= true_sum;
    if (c.hi != Int_MAX) c.hi -= true_sum;

    // Propagate:
    while (c.size > 0){
        if (c(c.size-1) > c.hi){
            addUnit(~c[c.size-1]);
            sum -= c(c.size-1);
            c.size--;
        }else if (sum - c(c.size-1) < c.lo){
            addUnit(c[c.size-1]);
            sum -= c(c.size-1);
            if (c.lo != Int_MIN) c.lo -= c(c.size-1);
            if (c.hi != Int_MAX) c.hi -= c(c.size-1);
            c.size--;
        }else
            break;
    }

    if (c.lo <= 0)  c.lo = Int_MIN;
    if (c.hi > sum) c.hi = Int_MAX;

    //**/reportf("AFTER propagate()\n");
    //**/dump(c, sat_solver.assigns_ref()); reportf("\n\n");
    if (c.size == 0){
        if (c.lo > 0 || c.hi < 0)
            sat_solver.addEmptyClause();
        return true;
    }else
        return c.lo == Int_MIN && c.hi == Int_MAX;
}


void PbSolver::propagate()
{
    if (nVars() == 0) return;
    if (occur.size() == 0) setupOccurs();

    if (opt_verbosity >= 2) reportf("  -- Unit propagations: ", constrs.size());
    bool found = false;

    while (propQ_head < trail.size()){
        //**/reportf("propagate("); dump(trail[propQ_head]); reportf(")\n");
        Var     x = var(trail[propQ_head++]);
        for (int pol = 0; pol < 2; pol++){
            vec<int>&   cs = occur[toInt(mkLit(x,pol))];
            for (int i = 0; i < cs.size(); i++){
                if (constrs[cs[i]] == NULL) continue;
                int trail_sz = trail.size();
                if (propagate(*constrs[cs[i]]))
                    constrs[cs[i]] = NULL;
                if (opt_verbosity >= 2 && trail.size() > trail_sz) found = true, reportf("p");
                if (!okay()) return;
            }
        }
    }

    if (opt_verbosity >= 2) {
        if (!found) reportf("(none)\n");
        else        reportf("\n");
    }

    occur.clear(true);
}


void PbSolver::setupOccurs()
{
    // Allocate vectors of right capacities:
    occur.growTo(nVars()*2);
    assert(nVars() == pb_n_vars);
    for (int i = 0; i < nVars()*2; i++){
        vec<int> tmp(xmalloc<int>(n_occurs[i]), n_occurs[i]); tmp.clear();
        tmp.moveTo(occur[i]); }

    // Fill vectors:
    for (int i = 0; i < constrs.size(); i++){
        if (constrs[i] == NULL) continue;
        for (int j = 0; j < constrs[i]->size; j++)
            assert(occur[toInt((*constrs[i])[j])].size() < n_occurs[toInt((*constrs[i])[j])]),
            occur[toInt((*constrs[i])[j])].push(i);
    }
}


// Left-hand side equal
static bool lhsEq(const Linear& c, const Linear& d) {
    if (c.size == d.size){
        for (int i = 0; i < c.size; i++) if (c[i] != d[i] || c(i) != d(i)) return false;
        return true;
    }else return false; }
// Left-hand side equal complementary (all literals negated)
static bool lhsEqc(const Linear& c, const Linear& d) {
    if (c.size == d.size){
        for (int i = 0; i < c.size; i++) if (c[i] != ~d[i] || c(i) != d(i)) return false;
        return true;
    }else return false; }


void PbSolver::findIntervals()
{
    if (opt_verbosity >= 2)
        reportf("  -- Detecting intervals from adjacent constraints: ");

    bool found = false;
    int i = 0;
    Linear* prev;
    for (; i < constrs.size() && constrs[i] == NULL; i++);
    if (i < constrs.size()){
        prev = constrs[i++];
        for (; i < constrs.size(); i++){
            if (constrs[i] == NULL) continue;
            Linear& c = *prev;
            Linear& d = *constrs[i];

            if (lhsEq(c, d)){
                if (d.lo < c.lo) d.lo = c.lo;
                if (d.hi > c.hi) d.hi = c.hi;
                constrs[i-1] = NULL;
                if (opt_verbosity >= 2) reportf("=");
                found = true;
            }
            if (lhsEqc(c, d)){
                Int sum = 0;
                for (int j = 0; j < c.size; j++)
                    sum += c(j);
                Int lo = (c.hi == Int_MAX) ? Int_MIN : sum - c.hi;
                Int hi = (c.lo == Int_MIN) ? Int_MAX : sum - c.lo;
                if (d.lo < lo) d.lo = lo;
                if (d.hi > hi) d.hi = hi;
                constrs[i-1] = NULL;
                if (opt_verbosity >= 2) reportf("#");
                found = true;
            }

            prev = &d;
        }
    }
    if (opt_verbosity >= 2) {
        if (!found) reportf("(none)\n");
        else        reportf("\n");
    }
}


bool PbSolver::rewriteAlmostClauses()
{
    vec<Lit>    ps;
    vec<Int>    Cs;
    bool        found = false;
    int         n_splits = 0;
    char        buf[20];

    if (opt_verbosity >= 2)
        reportf("  -- Clauses(.)/Splits(s): ");
    for (int i = 0; i < constrs.size(); i++){
        if (constrs[i] == NULL) continue;
        Linear& c   = *constrs[i];
        assert(c.lo != Int_MIN || c.hi != Int_MAX);

        if (c.hi != Int_MAX) continue;

        int n = c.size;
        for (; n > 0 && c(n-1) == c.lo; n--);

        if (n <= 1){
            // Pure clause:
            if (opt_verbosity >= 2) reportf(".");
            found = true;
            ps.clear();
            for (int j = n; j < c.size; j++)
                ps.push(c[j]);
            addClause(ps);

            constrs[i] = NULL;      // Remove this clause

        }else if (c.size-n >= 3){
            // Split clause part:
            if (opt_verbosity >= 2) reportf("s");
            found = true;
            sprintf(buf, "@split%d", n_splits);
            n_splits++;
            Var x = getVar(buf); assert(x == sat_solver.nVars()-1);
            ps.clear();
            ps.push(mkLit(x));
            for (int j = n; j < c.size; j++)
                ps.push(c[j]);
            addClause(ps);
            if (!okay()){
                reportf("\n");
                return false; }

            ps.clear();
            Cs.clear();
            ps.push(~mkLit(x));
            Cs.push(c.lo);
            for (int j = 0; j < n; j++)
                ps.push(c[j]),
                Cs.push(c(j));
            Lit lit = lit_Undef;
            if (!addConstr(ps, Cs, c.lo, 1, lit)){
                reportf("\n");
                return false; }

            constrs[i] = NULL;      // Remove this clause
        }
    }

    if (opt_verbosity >= 2) {
        if (!found) reportf("(none)\n");
        else        reportf("\n");
    }
    return true;
}


//=================================================================================================
// Main solver/optimizer:
extern MsSolver *pb_solver;
static
void SIGINT_interrupt(int /*signum*/) { pb_solver->sat_solver.interrupt(); pb_solver->asynch_interrupt=true; }

Int evalGoal(Linear& goal, vec<bool>& model)
{
    Int sum = 0;
    for (int i = 0; i < goal.size; i++){
        if (( sign(goal[i]) && model[var(goal[i])] == false)
        ||  (!sign(goal[i]) && model[var(goal[i])] == true )
        )
            sum += goal(i);
    }
    return sum;
}

void PbSolver::solve(solve_Command cmd)
{
    if (!okay()) {
        if (opt_verbosity >= 1) sat_solver.printVarsCls();
        return;
    }
#if defined(GLUCOSE3) || defined(GLUCOSE4)    
    if (opt_verbosity >= 1) sat_solver.verbEveryConflicts = 100000;
    sat_solver.setIncrementalMode();
#endif

    // Convert constraints:
    pb_n_vars = nVars();
    pb_n_constrs = constrs.size();
    if (opt_verbosity >= 1)
        reportf("Converting %d PB-constraints to clauses...\n", constrs.size());
    propagate();
    if (!convertPbs(true)){
        if (opt_verbosity >= 1) sat_solver.printVarsCls(constrs.size() > 0);
        assert(!okay()); return; 
    }

    // Freeze goal function variables (for SatELite):
    if (goal != NULL){
        for (int i = 0; i < goal->size; i++)
            sat_solver.setFrozen(var((*goal)[i]), true);
    }
    if (opt_maxsat) {
        vec<Pair<weight_t, Minisat::vec<Lit>* > > &soft_cls = ((MsSolver *)this)->soft_cls; 
        for (int i = soft_cls.size() - 1; i >= 0; i--)
            for (int j = soft_cls[i].snd->size() - 1; j >= 0; j--)
                sat_solver.setFrozen(var((*soft_cls[i].snd)[j]), true);
    }
    // Solver (optimize):
    //sat_solver.setVerbosity(opt_verbosity);
    sat_solver.verbosity = opt_verbosity - 1;
    Int goal_gcd;
    if (goal != NULL) {
        goal_gcd = (*goal)(0);
        for (int i = 1; i < goal->size; ++i) goal_gcd = gcd(goal_gcd, (*goal)(i));
        if (goal_gcd < 0) goal_gcd = -goal_gcd;
    }

    vec<Lit> goal_ps; if (goal != NULL){ for (int i = 0; i < goal->size; i++) goal_ps.push((*goal)[i]); }
    vec<Int> goal_Cs; if (goal != NULL){ for (int i = 0; i < goal->size; i++) goal_Cs.push((*goal)(i)/goal_gcd); }
    assert(best_goalvalue == Int_MAX);

    if (opt_polarity_sug != 0){
        for (int i = 0; i < goal_Cs.size(); i++){
            bool dir = goal_Cs[i]*opt_polarity_sug > 0 ? !sign(goal_ps[i]) : sign(goal_ps[i]);
            sat_solver.setPolarity(var(goal_ps[i]), LBOOL(dir));
        }
    }

    if (opt_convert_goal != ct_Undef)
        opt_convert = opt_convert_goal;
    opt_sort_thres *= opt_goal_bias;
    opt_shared_fmls = use_base_assump = true;
    Lit assump_lit = lit_Undef;

    if (opt_goal != Int_MAX)
        addConstr(goal_ps, goal_Cs, opt_goal, -1, assump_lit),
        convertPbs(false);

    if (opt_cnf != NULL)
        reportf("Exporting CNF to: \b%s\b\n", opt_cnf),
        sat_solver.toDimacs(opt_cnf),
        exit(0);

    signal(SIGINT, SIGINT_interrupt);
#ifdef SIGXCPU
    signal(SIGXCPU,SIGINT_interrupt);
#endif

    bool    sat = false;
    Minisat::vec<Lit> assump_ps;
    Int     try_lessthan = opt_goal;
    int     n_solutions = 0;    // (only for AllSolutions mode)

    LB_goalvalue = 0, UB_goalvalue = 0; 
    if (goal != NULL)
        for (int i = 0; i < goal_Cs.size(); ++i)
            if (value(goal_ps[i]) != l_Undef) {
                if (value(goal_ps[i]) == l_True)
                    LB_goalvalue += goal_Cs[i], UB_goalvalue += goal_Cs[i];
	    } else if (goal_Cs[i] < 0) LB_goalvalue += goal_Cs[i];
            else UB_goalvalue += goal_Cs[i];
    if (opt_minimization != 0 && goal != NULL && opt_goal == Int_MAX) {
        assump_lit = mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars));
        try_lessthan = (UB_goalvalue + LB_goalvalue)/2;
        if (addConstr(goal_ps, goal_Cs, try_lessthan, -2, assump_lit)) {
            if (!use_base_assump) assump_ps.push(assump_lit);
            convertPbs(false);
        }
    }
    if (opt_verbosity >= 1)
        sat_solver.printVarsCls();
    while (1) {
      if (use_base_assump) for (int i = 0; i < base_assump.size(); i++) assump_ps.push(base_assump[i]);
      lbool status = 
          base_assump.size() == 1 && base_assump[0] == assump_lit ? l_True :
          base_assump.size() == 1 && base_assump[0] == ~assump_lit ? l_False :
          sat_solver.solveLimited(assump_ps);
      if (use_base_assump) {
          for (int i = 0; i < base_assump.size(); i++) {
              if (status == l_True && var(base_assump[i]) < pb_n_vars) addUnit(base_assump[i]);
              assump_ps.pop();
          }
          base_assump.clear();
      }
      if (status  == l_Undef) {
        if (asynch_interrupt) { reportf("*** Interrupted ***\n"); break; }
      } else if (status == l_True) { // SAT returned
        if(assump_ps.size() > 0) {
          assert(assump_ps.size() == 1);
          addUnit(assump_ps[0]);
        }
        assump_ps.clear();
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
            if (goal == NULL) {
                model.moveTo(best_model);
                break;
            }
            Int goalvalue = (opt_maxsat ? evalGoal(((MsSolver *)this)->soft_cls, model, soft_unsat) : evalGoal(*goal, model)) / goal_gcd;
            if (goalvalue < best_goalvalue) {
                best_goalvalue = goalvalue;
                model.moveTo(best_model);
                char* tmp = toString(best_goalvalue * goal_gcd);
                if (opt_satlive || opt_verbosity == 0)
                    printf("o %s\n", tmp), fflush(stdout);
                else reportf("\bFound solution: %s\b\n", tmp);
                xfree(tmp);
            } else model.clear();
            if (best_goalvalue < UB_goalvalue) UB_goalvalue = best_goalvalue;

            if (cmd == sc_FirstSolution) break;

            if (opt_verbosity >= 1 && !opt_satlive){
                char* tmp = toString(best_goalvalue * goal_gcd);
                reportf("\bFound solution: %s\b\n", tmp);
                xfree(tmp); }
            if(opt_minimization == 0 || best_goalvalue - LB_goalvalue < opt_seq_thres) {
                assump_lit = lit_Undef;
                try_lessthan = best_goalvalue;
            } else {
                assump_lit = assump_lit == lit_Undef || !use_base_assump ?
                    mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars)) : assump_lit;
                try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;
            }
            if (!addConstr(goal_ps, goal_Cs, try_lessthan, -2, assump_lit))
                break; // unsat
            if (assump_lit != lit_Undef && !use_base_assump) assump_ps.push(assump_lit);
            convertPbs(false);
        }
      } else { // UNSAT returned

        if (assump_lit == lit_Undef) break;

        if (assump_ps.size() == 1) addUnit(~(assump_ps[0]));
        assump_ps.clear();
        LB_goalvalue = try_lessthan;

	if(opt_minimization != 2 || best_goalvalue == Int_MAX || best_goalvalue - LB_goalvalue < opt_seq_thres) {
            assump_lit = lit_Undef;
            try_lessthan = (best_goalvalue != Int_MAX ? best_goalvalue : UB_goalvalue+1);
	} else {
            assump_lit = assump_lit == lit_Undef || !use_base_assump ?
                mkLit(sat_solver.newVar(VAR_UPOL, !opt_branch_pbvars)) : assump_lit;
            try_lessthan = (LB_goalvalue*(100-opt_bin_percent) + best_goalvalue*(opt_bin_percent))/100;
	}
        if (!addConstr(goal_ps, goal_Cs, try_lessthan, -2, assump_lit))
            break; // unsat
        if (assump_lit != lit_Undef && !use_base_assump) assump_ps.push(assump_lit);
        if (opt_minimization >= 1 && opt_verbosity >= 2) {
            char *tmp; reportf("Lower bound  = %s\n", tmp = toString(LB_goalvalue)); xfree(tmp); }
        convertPbs(false);
      }         
    } // END OF LOOP

    if (goal == NULL && sat)
        best_goalvalue = Int_MIN;       // (found model, but don't care about it)
    if (opt_verbosity >= 1){
        if      (!sat)
            reportf(asynch_interrupt ? "\bUNKNOWN\b\n" : "\bUNSATISFIABLE\b\n");
        else if (goal == NULL)
            reportf("\bSATISFIABLE: No goal function specified.\b\n");
        else if (cmd == sc_FirstSolution){
            char* tmp = toString(best_goalvalue * goal_gcd);
            reportf("\bFirst solution found: %s\b\n", tmp);
            xfree(tmp);
        }else if (asynch_interrupt){
            char* tmp = toString(best_goalvalue * goal_gcd);
            reportf("\bSATISFIABLE: Best solution found: %s\b\n", tmp);
            xfree(tmp);
       }else{
            char* tmp = toString(best_goalvalue * goal_gcd);
            reportf("\bOptimal solution: %s\b\n", tmp);
            xfree(tmp);
        }
    }
}

void PbSolver::printStats(bool printSatStats)
{
#ifdef USE_SCIP
    std::lock_guard<std::mutex> lck(stdout_mtx);
#endif
    static bool statsPrinted = false;
    if (!statsPrinted) {
        double cpu_time = cpuTime();
        double mem_used = memUsedPeak();
      if (printSatStats) {
        printf("c _______________________________________________________________________________\nc \n");
#if defined(CADICAL) || defined(CRYPTOMS)
        sat_solver.statistics();
#else
        printf("c restarts               : %" PRIu64"\n", sat_solver.starts);
        printf("c conflicts              : %-12" PRIu64"   (%.0f /sec)\n", sat_solver.conflicts   , sat_solver.conflicts   /cpu_time);
        printf("c decisions              : %-12" PRIu64"   (%4.2f %% random) (%.0f /sec)\n", sat_solver.decisions, (float)sat_solver.rnd_decisions*100 / (float)sat_solver.decisions, sat_solver.decisions   /cpu_time);
        printf("c propagations           : %-12" PRIu64"   (%.0f /sec)\n", sat_solver.propagations, sat_solver.propagations/cpu_time);
        printf("c conflict literals      : %-12" PRIu64"   (%4.2f %% deleted)\n", sat_solver.tot_literals, (sat_solver.max_literals - sat_solver.tot_literals)*100 / (double)sat_solver.max_literals);
#endif
      }
        printf("c =======================[ UWrMaxSat resources usage ]===========================\n");
        if (mem_used != 0) printf("c Memory used            : %.2f MB\n", mem_used);
        printf("c CPU time               : %g s\n", cpu_time);
#ifdef USE_SCIP
        extern bool opt_scip_parallel;
        extern time_t wall_clock_time;
        if (opt_scip_parallel)
            printf("c Wall clock time        : %g s\n", difftime(time(NULL), wall_clock_time));
#endif
        if (srtEncodings != 0 || bddEncodings != 0 || addEncodings != 0)
            printf("c Constr Enc: Srt/BDD/Add: %llu %llu %llu\n", srtEncodings, bddEncodings, addEncodings);
        if (srtOptEncodings != 0 || bddOptEncodings != 0 || addOptEncodings != 0)
            printf("c OptExp Enc: Srt/BDD/Add: %llu %llu %llu\n", srtOptEncodings, bddOptEncodings, addOptEncodings);
        if (totalSorters > 0 && totalReusedInputs > 0.0)
            printf("c Reused sorter inputs   : %.0f of %.0f inputs (%.2f%% in avg) in %d sorters\n", totalReusedInputs, totalSorterInputs, totalReusedInputs*100.0/totalSorterInputs, totalSorters); 
        printf("c _______________________________________________________________________________\n");
        statsPrinted = true;
    }
}

