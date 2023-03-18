/*************************************************************************************[PbSolver.cc]
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

#ifndef CryptoMSWrap_h
#define CryptoMSWrap_h

#include "cryptominisat5/cryptominisat.h"
constexpr CMSat::lbool ll_Undef = CMSat::l_Undef;
constexpr CMSat::lbool ll_True  = CMSat::l_True;
constexpr CMSat::lbool ll_False = CMSat::l_False;
#include "mtl/Vec.h"
#include "core/SolverTypes.h"

namespace COMinisatPS {

class SimpSolver {
protected:
    CMSat::SATSolver *solver;
private:
    vec<lbool> fixedVars;
    int nclauses, old_verbosity;
    bool firstCall;

    CMSat::Lit CMLit(Lit p) { return CMSat::Lit(var(p), sign(p)); }
    Lit        MSLit(CMSat::Lit p) { return mkLit(p.var(), p.sign()); }

    void before_solve() {
        if (firstCall) {
            firstCall = false; printf("c Using CryptoMiniSat(ver. %s) SAT solver by its Authors (2020)\n", solver->get_version()); }
        if (verbosity < 0) verbosity = 0; else if (verbosity > 3) verbosity = 3;
        if (verbosity != old_verbosity) solver->set_verbosity(old_verbosity = verbosity);
    }
    void after_solve() {
        std::vector<CMSat::Lit> zeroFixed = solver->get_zero_assigned_lits();

        fixedVars.clear(); fixedVars.growTo(solver->nVars(), l_Undef);
        for (CMSat::Lit p : zeroFixed)
            if ((int)p.var() < fixedVars.size()) fixedVars[p.var()] = (p.sign() ? l_True : l_False);
    }

public:
    vec<Lit> conflict;
    int verbosity;
    uint64_t conflicts;

    SimpSolver() : nclauses(0), firstCall(true), conflicts(0) {
        solver = new CMSat::SATSolver;
        solver->set_num_threads(1);
        verbosity = old_verbosity = 0;
    }
    ~SimpSolver() { delete solver; }

    Var newVar(bool polarity = true, bool dvar = true) {
        (void)polarity; (void)dvar;
        solver->new_var();
        Var v = solver->nVars() - 1;
        return v;
    }
    int  nVars() const { return solver->nVars(); }
    int  nClauses() const { return nclauses; }
    void setPolarity(Var, bool) { /* unsupported */ }
    void setFrozen(Var , bool ) { /* not required */ }

    bool addClause(const vec<Lit>& c) {
        std::vector<CMSat::Lit> cl;
        for (int i = 0; i < c.size(); i++) cl.push_back(CMLit(c[i]));
        nclauses++; return solver->add_clause(cl); 
    }
    bool addEmptyClause() {
        std::vector<CMSat::Lit> cl;
        nclauses++; return solver->add_clause(cl); }
    bool addClause(Lit p) {
        std::vector<CMSat::Lit> cl;
        cl.push_back(CMLit(p)); nclauses++; return solver->add_clause(cl); }
    bool addClause(Lit p, Lit q) { 
        std::vector<CMSat::Lit> cl;
        cl.push_back(CMLit(p)); cl.push_back(CMLit(q)); nclauses++; return solver->add_clause(cl); }
    bool addClause(Lit p, Lit q, Lit r) { 
        std::vector<CMSat::Lit> cl;
        cl.push_back(CMLit(p)); cl.push_back(CMLit(q)); cl.push_back(CMLit(r)); nclauses++; 
        return solver->add_clause(cl); }
    bool addClause_(vec<Lit>& cl) { return addClause(cl); }

    bool okay() { return solver->okay(); }

    void interrupt() { solver->interrupt_asap(); }
    void clearInterrupt() { }

    void setConfBudget(int x) { solver->set_max_confl(x); }
    void budgetOff() { solver->set_max_confl(0); }

    lbool solveLimited() {
        before_solve();
        CMSat::lbool ret = solver->solve();
        //after_solve();
        conflicts = solver->get_sum_conflicts();
        return ret==ll_Undef ? l_Undef : ret==ll_True ? l_True : l_False;
    }
    bool solve() {
        budgetOff();
        lbool ret = solveLimited();
        assert(ret != l_Undef);
        return ret == l_True;
    }
    lbool solveLimited(const vec<Lit>& assumps) {
        std::vector<CMSat::Lit> a;
        for (int i = 0; i < assumps.size(); i++)
            if (toInt(assumps[i]) >= 0) a.push_back(CMLit(assumps[i]));
        before_solve();
        CMSat::lbool ret = solver->solve(&a);
        //after_solve();
        if (ret == ll_False) {
            conflict.clear();
            std::vector<CMSat::Lit> confl = solver->get_conflict();
            for (unsigned i = 0; i < confl.size(); i++) conflict.push(MSLit(confl[i]));
        }
        conflicts = solver->get_sum_conflicts();
        return ret==ll_Undef ? l_Undef : ret==ll_True ? l_True : l_False;
    }
    bool solve(const vec<Lit>& assumps) {
        budgetOff();
        lbool ret = solveLimited(assumps);
        assert(ret != l_Undef);
        return ret == l_True;
    }
    bool eliminate(bool turn_off_elim = false) { 
        CMSat::lbool ret = solver->simplify();
        if (turn_off_elim) solver->set_no_simplify();
        return ret != ll_False; 
    }
    bool isEliminated(Var) { /* not needed */ return false; }

    lbool value(Var v) const { return v < fixedVars.size() ? fixedVars[v] : l_Undef; }
    lbool value(Lit p) const { return var(p) < fixedVars.size() && fixedVars[var(p)] != l_Undef ? fixedVars[var(p)] ^ sign(p) : l_Undef; }

    lbool modelValue(Var v) const { 
        CMSat::lbool ret = solver->get_model()[v]; 
        return ret==ll_Undef ? l_Undef : ret==ll_True ? l_True : l_False;
    }
    lbool modelValue(Lit p) const {
        lbool val = modelValue(var(p));
        if (sign(p)) 
            if (val == l_True) val = l_False; else if (val == l_False) val = l_True;
        return val;
    }

    void toDimacs(const char *file) { solver->open_file_and_dump_irred_clauses(file); }
    void statistics() { solver->print_stats(); }
    void setTermCallback(void * /*state*/, int (* /*terminate*/)(void *)) { /* this is complicated */ }
};

}

#endif
