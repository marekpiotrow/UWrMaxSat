/*************************************************************************************[PbSolver.cc]
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

#include "SatSolver.h"

#if !defined(CADICAL) && !defined(CRYPTOMS)
static Var mapVar(Var x, Minisat::vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}
#endif

#if !defined(CADICAL) && !defined(CRYPTOMS)
const Minisat::Clause& ExtSimpSolver::getClause  (int i, bool &is_satisfied) const
{
    const Minisat::Clause& ps = ca[clauses[i]];
    is_satisfied = ps.mark() != 0 || satisfied(ps);
    return ps;
}
#endif

void ExtSimpSolver::reduceProblem()
{
#if !defined(CADICAL) && !defined(CRYPTOMS)
    if (use_simplification) eliminate();
    elimclauses.copyTo(elimClauses);
#endif
}

#if !defined(CADICAL) && !defined(CRYPTOMS)
void ExtSimpSolver::extendGivenModel(vec<lbool> &model)
{
    for (int j, i = elimClauses.size()-1; i > 0; i -= j) {
        Lit x;
        for (j = elimClauses[i--]; j > 1; j--, i--) {
            x = Minisat::toLit(elimClauses[i]);
            if ((model[var(x)] ^ sign(x)) != l_False) goto next; // x is no false in the model
        }
        x = Minisat::toLit(elimClauses[i]);
        model[var(x)] = lbool(!sign(x));
next:;
    }
}
#else
void ExtSimpSolver::extendGivenModel(vec<lbool> &) {}
#endif

void ExtSimpSolver::printVarsCls(bool encoding, const vec<Pair<weight_t, Minisat::vec<Lit>* > > *soft_cls, int soft_cnt)
{
    Minisat::vec<Var> map; Var max=0;
    int cnt;

#ifdef CADICAL
    max = solver->active();
    cnt = solver->irredundant();
    (void)soft_cls;
#elif defined(CRYPTOMS)
    max = solver->nVars();
    cnt = nClauses();
    (void)soft_cls;
#else
    if (!ok) max=1, cnt=2;
    else {
        cnt = 0; // assumptions.size();
        for (int i = 0; i < clauses.size(); i++)
          if (!satisfied(ca[clauses[i]])) {
	      cnt++;
              Minisat::Clause& c = ca[clauses[i]];
	      for (int j = 0; j < c.size(); j++)
	          if (value(c[j]) != l_False)
	              mapVar(var(c[j]), map, max);
        }
        if (soft_cls != NULL)
            for (int i = 0; i < soft_cls->size(); i++) {
                Minisat::vec<Lit>& c = *(*soft_cls)[i].snd;
                for (int j = 0; j < c.size(); j++)
	            if (value(c[j]) != l_False)
	                mapVar(var(c[j]), map, max);
            }

    }
#endif
    printf("c ============================[ %s Statistics ]============================\n", 
            encoding ? "Encoding" : " Problem");
    printf("c |  Number of variables:  %12d                                         |\n", max);
    if (soft_cnt == 0)
        printf("c |  Number of clauses:    %12d                                         |\n", cnt);
    else
        printf("c |  Number of clauses:    %12d (incl. %12d soft in queue)      |\n", cnt + soft_cnt, soft_cnt);
    printf("c ===============================================================================\n");
}

//=================================================================================================
// Propagate and check:
#if defined(CADICAL) || defined(CRYPTOMS)
bool ExtSimpSolver::prop_check(Lit assump, Minisat::vec<Lit>& prop, int )
{
    prop.clear(); prop.push(assump);
    return okay();
}
#elif defined(MERGESAT)
bool ExtSimpSolver::prop_check(Lit assump, Minisat::vec<Lit>& prop, int )
{
    if (!ok || propagateLit(assump, prop)) return false; 
    prop.push(assump);
    return true;
}
#else
bool ExtSimpSolver::prop_check(Lit assump, Minisat::vec<Lit>& prop, int psaving)
{
    using Minisat::CRef; using Minisat::CRef_Undef;
    prop.clear();

    if (!ok) return false;
    if (value(assump) != l_Undef) return value(assump) == l_True;

    CRef confl = CRef_Undef;

    // dealing with phase saving
    int psaving_copy = phase_saving;
    phase_saving = psaving;

    // propagate assumption at a new decision level
#ifdef MAPLE
    int trailRec = trailRecord;
    trailRecord = trail.size();
    Solver::simpleUncheckEnqueue(assump);
    confl = Solver::simplePropagate();
    if (confl == CRef_Undef && trail.size() > trailRecord) { // copying the result
        int c = trailRecord;
        if (trail[c] == assump) c++;
        while (c < trail.size()) prop.push(trail[c++]);
    }
    cancelUntilTrailRecord(); // backtracking
    trailRecord = trailRec;
#else
    int  level = decisionLevel();
    Solver::newDecisionLevel ();
    Solver::uncheckedEnqueue(assump);
    confl = Solver::propagate();
    if (confl == CRef_Undef) { // copying the result
        int c = trail_lim[level];
        if (trail[c] == assump) c++;
        while (c < trail.size()) prop.push(trail[c++]);
    }
    Solver::cancelUntil(level); // backtracking
#endif

    // restoring phase saving
    phase_saving = psaving_copy;

    return confl == CRef_Undef;
}
#endif
