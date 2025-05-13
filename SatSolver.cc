/*************************************************************************************[PbSolver.cc]
KP-MiniSat+ based on MiniSat+ -- Copyright (c) 2018-2020 Michał Karpiński, Marek Piotrów

UWrMaxSat based on KP-MiniSat+ -- Copyright (c) 2019-2024 Marek Piotrów

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
#include "Debug.h"
#include "Sort.h"

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

bool ExtSimpSolver::reduceProblem(int level)
{
    bool res = true;
#if defined(CADICAL)
    if (level != 0) solver->optimize(level);
    res = eliminate(false);
    solver->traverse_witnesses_forward(extendIt);
    extendIt.elimCls.moveTo(elimClauses);
    if (level != 0) solver->optimize(0);
#elif !defined(CRYPTOMS)
    (void)level;
    if (use_simplification) res = eliminate();
    elimclauses.copyTo(elimClauses);
#endif
    return res;
}

void ExtSimpSolver::extendGivenModel(vec<lbool> &model)
{
#if defined(CADICAL)
    for (int i = model.size() - 1; i >= 0; i--)
        if (model[i] == l_Undef) model[i] = l_False;
    for (int j, i = elimClauses.size()-1; i > 0; i -= j) {
        Lit x;
        for (j = elimClauses[i--]; j > 0; j--, i--) { // clause processing
            x = Minisat::toLit(elimClauses[i]);
            if ((model[var(x)] ^ sign(x)) == l_True) { // the clause is satisfied
                i -= elimClauses[i-j] + 1; // skip witnesses
                goto next;             }
        }
        for (j = elimClauses[i--]; j > 0; j--, i--) { // witnesses processing
            x = Minisat::toLit(elimClauses[i]);
            if ((model[var(x)] ^ sign(x)) != l_True) //  x is not satisfied
                model[var(x)] = (model[var(x)] == l_True ? l_False : l_True); // x is flipped
        }
next:;
    }
#elif !defined(CRYPTOMS)
    for (int j, i = elimClauses.size()-1; i > 0; i -= j) {
        Lit x;
        for (j = elimClauses[i--]; j > 1; j--, i--) {
            x = Minisat::toLit(elimClauses[i]);
            if ((model[var(x)] ^ sign(x)) != l_False) goto next; // x is not false in the model
        }
        x = Minisat::toLit(elimClauses[i]);
        model[var(x)] = lbool(!sign(x));
next:;
    }
#else
    (void)model;
#endif
}

void ExtSimpSolver::optimizeModel(const vec<Pair<weight_t, Minisat::vec<Lit>* > >& soft_cls,
        vec<bool>& model, int from_soft, int to_soft)
{
#if defined(CADICAL)
    extern bool satisfied_soft_cls(Minisat::vec<Lit> *cls, vec<bool>& model);
    Int sum = 0;
    bool sat = false, opt = false;
    for (int i = to_soft; i >= from_soft; i--) {
        Lit p = soft_cls[i].snd->last(); if (soft_cls[i].snd->size() == 1) p = ~p;
        assert(var(p) < model.size());
        if ((( sign(p) && !model[var(p)]) || (!sign(p) &&  model[var(p)])) 
            && !(sat = satisfied_soft_cls(soft_cls[i].snd, model))) {
            if (solver->flip(var(p) + 1)) model[var(p)] = !model[var(p)], opt = true;
        }
        if (sat) { sat = false; model[var(p)] = !model[var(p)]; }
    }
    if (opt)
        for (int v = model.size() - 1 ; v >= 0; v--) model[v] = solver->val(v + 1) > 0;
#endif
}

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
    fflush(stdout);
}

//=================================================================================================
#if defined(CADICAL)
void ExtSimpSolver::startPropagator(const Minisat::vec<Lit>& observed)
{
    extPropagator = new LitPropagator();
    solver->connect_external_propagator(extPropagator);
    for (int i = 0; i < observed.size(); i++)
        solver->add_observed_var(abs(lit2val(observed[i])));
}

void ExtSimpSolver::stopPropagator()
{
    solver->disconnect_external_propagator();
    delete extPropagator;
    extPropagator = nullptr;
}
#else
void ExtSimpSolver::startPropagator(const Minisat::vec<Lit>&) {}
void ExtSimpSolver::stopPropagator() {}
#endif

// Find all implied literals from a given literal lit with respect to given possible assumptions 
#if defined(CRYPTOMS)
bool ExtSimpSolver::impliedObservedLits(Lit , Minisat::vec<Lit>& props, const vec<Lit>& , int )
{
    // not implemented
    props.clear();
    return okay();

}
#elif defined(CADICAL)
bool ExtSimpSolver::impliedObservedLits(Lit lit, Minisat::vec<Lit>& props, const vec<Lit>& assumps, int )
{
    props.clear();
    if (!okay()) return false;
    if (value(lit) != l_Undef) return value(lit) == l_True;
    for (int i = 0; i < assumps.size(); i++)
        if (value(assumps[i]) == l_False) return true;

    for (int i = 0; i < assumps.size(); i++)
        if (value(assumps[i]) != l_True && toInt(assumps[i]) >= 0) solver->assume(lit2val(assumps[i]));
    solver->assume(lit2val(lit));

    solver->limit ("decisions", 1); // set decision limit to one
    lbool ret = solveLimited();

    if (ret != l_False && extPropagator->dec_level > 1) {
        for (const int clit : extPropagator->last_trails[1 - extPropagator->dec_level % 2]) {
            if (clit != 0) {
                Lit l = mkLit(abs(clit) - 1, clit < 0);
                if (l != lit) props.push(l);
            }
        }
    }
    return ret != l_False;
}
#elif defined(MERGESAT)
bool ExtSimpSolver::impliedObservedLits(Lit lit, Minisat::vec<Lit>& props, const vec<Lit>& assumptions, int )
{
    if (value(lit) != l_Undef) return value(lit) == l_True;

    Solver::cancelUntil(0);
    if (assumptions.size() > 0) {
        while (decisionLevel() < assumptions.size()) {
            Lit p = assumptions[decisionLevel()];
            if (value(p) == l_False) {
                Solver::cancelUntil(0);
                return true;
            }
            Solver::newDecisionLevel();
            if (value(p) == l_Undef) Solver::uncheckedEnqueue(p, decisionLevel(), Minisat::CRef_Undef);
        }
        if (Solver::propagate() != Minisat::CRef_Undef) {
            Solver::cancelUntil(0);
            return true;
        }
    }
    bool noConflict = true;
    Solver::newDecisionLevel();
    Solver::uncheckedEnqueue(lit, decisionLevel(), Minisat::CRef_Undef);

    int c = trail.size();
    if (!ok || (Solver::propagate() != Minisat::CRef_Undef)) noConflict = false;
    else  // collect trail literals
        for ( ; c < trail.size() ; c++)
            props.push(trail[c]);
    Solver::cancelUntil(0);
    return noConflict;
}
#else
bool ExtSimpSolver::impliedObservedLits(Lit lit, Minisat::vec<Lit>& props, const vec<Lit>& assumptions, int psaving)
{
    using Minisat::CRef; using Minisat::CRef_Undef;
    props.clear();

    if (!ok) return false;
    if (value(lit) != l_Undef) return value(lit) == l_True;

    CRef confl = CRef_Undef;

    // dealing with phase saving
    int psaving_copy = phase_saving;
    phase_saving = psaving;

    // propagate lit at a new decision level
#ifdef MAPLE
    int trailRec = trailRecord;
    trailRecord = trail.size();
    if (assumptions.size() > 0) {
        Solver::newDecisionLevel ();
        for (int i = 0; i < assumptions.size(); i++) {
            Lit p = assumptions[i];
            if (value(p) == l_False) {
                Solver::cancelUntilTrailRecord(); // backtracking
                trailRecord = trailRec;
                phase_saving = psaving_copy;
                return true;
            }
            else if (value(p) != l_True) Solver::simpleUncheckedEnqueue(p);
        }
        confl = Solver::simplePropagate();
    }
    int newTrailRec = trail.size();
    Solver::simpleUncheckEnqueue(lit);
    confl = Solver::simplePropagate();
    if (confl == CRef_Undef && trail.size() > newTrailRecord) { // copying the result
        int c = newTrailRecord;
        if (trail[c] == lit) c++;
        for ( ; c < trail.size() ; c++)
            props.push(trail[c]);
    }
    cancelUntilTrailRecord(); // backtracking
    trailRecord = trailRec;
#else
    int old_level = decisionLevel();
    if (assumptions.size() > 0) {
        Solver::newDecisionLevel ();
        for (int i = 0; i < assumptions.size(); i++) {
            Lit p = assumptions[i];
            if (value(p) == l_False) {
                Solver::cancelUntil(old_level); // backtracking
                phase_saving = psaving_copy;
                return true;
            }
            else if (value(p) != l_True) uncheckedEnqueue(p);
        }
        confl = Solver::propagate();
    }
    if (confl == CRef_Undef && value(lit) == l_Undef) {
        int level = decisionLevel();
        Solver::newDecisionLevel ();
        Solver::uncheckedEnqueue(lit);
        confl = Solver::propagate();
        if (confl == CRef_Undef) { // copying the result
            int c = trail_lim[level];
            if (trail[c] == lit) c++;
            for ( ; c < trail.size() ; c++)
                props.push(trail[c]);
//if (props.size() > 0) { printf("IMPLIED %d literals from %s%d at level %d: ", props.size(), (sign(lit) ? "~" : ""), var(lit), level+1); vec<Lit> ps(props.size()); for(int i=0; i < props.size(); i++) ps[i]=props[i]; Sort::sort(ps); dump(ps); putchar('\n'); }
;
        }
    }
    Solver::cancelUntil(old_level); // backtracking
#endif

    // restoring phase saving
    phase_saving = psaving_copy;

    return confl == CRef_Undef;
}
#endif
