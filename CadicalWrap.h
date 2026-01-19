/*************************************************************************************[PbSolver.cc]
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

#ifndef CadicalWrap_h
#define CadicalWrap_h

#include "cadical.hpp"
#include "signal.hpp"
#include "mtl/Vec.h"
#include "core/SolverTypes.h"

extern int opt_cpu_lim;
extern int opt_minimization;
extern void set_interrupted(bool cpu_interrupted);

namespace COMinisatPS {

class SimpSolver {
public:
    CaDiCaL::Solver *solver;

    class AlarmTerm : public CaDiCaL::Handler, public CaDiCaL::Terminator {
    public:
        volatile static bool timesup;

        // Handler interface.
        void catch_signal (int ) { set_interrupted(false); }
        void catch_alarm () { timesup = true; set_interrupted(true); }
        // Terminator interface.
        bool terminate() { return timesup; }
    } alarm_term;

  
private:
    int nvars, nclauses, old_verbosity;
    vec<int> model;
    vec<int> var_offset, // offsets between CaDiCaL vars and the corresponding MiniSat vars
             var_counts; // var_counts[i]: the number of variables with offset <= var_offset[i]

    class IpasirTerm : public CaDiCaL::Terminator {
    public:
        void * state;
        int (*function) (void *);

        IpasirTerm() : state(nullptr), function(nullptr) {}
        bool terminate () { return function == nullptr ? false : function(state); }
    } terminator;

public:
    vec<Lit> conflict;
    int verbosity;
    uint64_t conflicts;

    SimpSolver() : nvars(0), nclauses(0), conflicts(0) {
        solver = new CaDiCaL::Solver;
        limitTime(opt_cpu_lim);
        verbosity = old_verbosity = solver->get("verbose");
        var_offset.push(1);
        var_counts.push(0);
        solver->set("seed",0);
        solver->set("stats",0);
        solver->prefix("c [CDCL] ");
#if CADICAL_MAJOR >= 3
        solver->set("luckyassumptions",0);
        solver->set("deduplicateallinit",1);
        solver->set("factor",1);
#endif        
    }
    ~SimpSolver() { delete solver; }

    int lit2val(Lit p) {
        int i = 0;
        while (i < var_counts.size() && var(p) >= var_counts[i]) i++;
        return sign(p) ? -var(p) - var_offset[i] : var(p) + var_offset[i];
    }

    Var cadical_declared_var(int v) {
        if (v <= 0 || v >= var_counts.last() + var_offset.last()) return var_Undef;
        int i = 0;
        while (v >= var_counts[i] + var_offset[i]) i++;
        return i > 0 && abs(v) < var_counts[i - 1] + var_offset[i] ? var_Undef : v - var_offset[i];
    }

    Lit val2lit(int v) {
        Var p = cadical_declared_var(abs(v));
        return p == var_Undef ? lit_Undef : mkLit(p, v < 0);
    }

    void limitTime(int time_limit) {
        alarm_term.timesup = false;
#if !defined(_MSC_VER) && !defined(__MINGW32__)
        CaDiCaL::Signal::reset_alarm();
        if (time_limit != INT32_MAX) {
            CaDiCaL::Signal::alarm(time_limit - int(cpuTime()));
            CaDiCaL::Signal::set(&alarm_term);
            solver->connect_terminator(&alarm_term);
        } else CaDiCaL::Signal::alarm(0);
#else
        (void)time_limit;
#endif
    }

    void setTermCallback(void * state, int (*terminate)(void *)) {
        terminator.state = state; terminator.function = terminate;
        if (terminator.function != nullptr) solver->connect_terminator(&terminator);
        else solver->disconnect_terminator();
    }

    class ExtendIterator : public CaDiCaL::WitnessIterator {
    public:
        vec<uint32_t> elimCls;
    public:
#if CADICAL_MAJOR >= 3
        bool witness (const std::vector<int> &cl, const std::vector<int> &witness, int64_t ) {
#else
        bool witness (const std::vector<int> &cl, const std::vector<int> &witness, uint64_t ) {
#endif
            for (const int w : witness) elimCls.push(toInt(mkLit(abs(w) - 1, w < 0)));
            elimCls.push(witness.size());
            for (const int c : cl) elimCls.push(toInt(mkLit(abs(c) - 1, c < 0)));
            elimCls.push(cl.size());
            return true;
        }
    } extendIt;

    Var newVar(bool polarity = true, bool dvar = true) {
        (void)polarity; (void)dvar;
        Var evar = nvars++;
#if CADICAL_MAJOR >= 3
        int cvar = solver->declare_one_more_variable(); // CaDiCaL new var
#else
        int cvar = nvars;
        solver->reserve((cvar));
#endif
        if (cvar == var_counts.last() + var_offset.last()) var_counts.last()++;
        else {
            var_offset.push(cvar - var_counts.last());
            var_counts.push(var_counts.last() + 1);
        }
        return evar;
    }
    int  nVars() const { return solver->vars(); }
    int  nFreeVars() const { return solver->active(); }
    int  nClauses() const { return solver->irredundant(); }
    void setPolarity(Var p, bool b) {
        (void)p; (void)b;
        //int x = lit2val(mkLit(p));
        //solver->phase(b ? x : -x);
    }
    void setFrozen(Var p, bool set) {
        int x = lit2val(mkLit(p));
        if (set) solver->freeze(x);
        else if (solver->frozen(x)) solver->melt(x);
    }

    bool addClause(const vec<Lit>& cl) {
        for (int i = 0; i < cl.size(); i++) solver->add(lit2val(cl[i]));
        solver->add(0); nclauses++; return true;
    }
    bool addEmptyClause() { 
        solver->add(0); nclauses++; return true; }
    bool addClause(Lit p) { 
        solver->add(lit2val(p)); solver->add(0); nclauses++; return true; }
    bool addClause(Lit p, Lit q) { 
        solver->add(lit2val(p)); solver->add(lit2val(q)); solver->add(0); nclauses++; return true; }
    bool addClause(Lit p, Lit q, Lit r) { 
        solver->add(lit2val(p)); solver->add(lit2val(q)); solver->add(lit2val(r)); solver->add(0);
        nclauses++; return true; }
    bool addClause_(vec<Lit>& cl) { return addClause(cl); }

    bool okay() { return ! solver->inconsistent(); }

    void interrupt() { solver->terminate(); }
    void clearInterrupt() { }

    void setConfBudget(int64_t x) { solver->limit("conflicts", x); }
    void budgetOff() { solver->limit("conflicts", -1); }

    lbool solveLimited(bool do_simp = true) {
        if (verbosity < 0) verbosity = 0; else if (verbosity > 3) verbosity = 3;
        if (verbosity != old_verbosity) solver->set("verbose", old_verbosity = verbosity);

        model.clear();
        (void)do_simp;
        int ret = solver->solve();
        conflicts = solver->conflicts();
        if (ret == 10) {
            int nv = nvars;
            model.growTo(nv);
            for (int v = 0 ; v < nv; v++) model[v] = solver->val(lit2val(mkLit(v)));
        }
        return ret == 10 ? l_True : (ret == 20 ? l_False : l_Undef);
    }
    bool solve(bool do_simp = true) {
        budgetOff();
        lbool ret = solveLimited(do_simp);
        assert(ret != l_Undef);
        return ret == l_True;
    }
    lbool solveLimited(const vec<Lit>& assumps, bool do_simp = true) {
        for (int i = 0; i < assumps.size(); i++)
            if (toInt(assumps[i]) >= 0) solver->assume(lit2val(assumps[i]));
        lbool ret = solveLimited(do_simp);
        if (ret == l_False) {
            conflict.clear();
            for (int i = 0; i < assumps.size(); i++)
                if (toInt(assumps[i]) >= 0 && solver->failed(lit2val(assumps[i]))) conflict.push(~assumps[i]);
        }
        return ret;
    }
    bool solve(const vec<Lit>& assumps, bool do_simp = true) {
        budgetOff();
        lbool ret = solveLimited(assumps, do_simp);
        assert(ret != l_Undef);
        return ret == l_True;
    }
    bool eliminate(bool) { return solver->simplify() != 20; }
    bool isEliminated(Var) { /* not needed */ return false; }

    lbool value(Var v) {
        int cvar = lit2val(mkLit(v));
        int val = solver->fixed(cvar);
        return val == 0 ? l_Undef : (val > 0 ? l_True : l_False);
    }
    lbool value(Lit p) {
        lbool val = value(var(p));
        if (sign(p)) 
            if (val == l_True) val = l_False; else if (val == l_False) val = l_True;
        return val;
    }

    lbool modelValue(Var v) {
        int val = (v < model.size() ? model[v] : 0);
        return val == 0 ? l_Undef : (val > 0 ? l_True : l_False);
    }
    lbool modelValue(Lit p) {
        lbool val = modelValue(var(p));
        if (sign(p)) 
            if (val == l_True) val = l_False; else if (val == l_False) val = l_True;
        return val;
    }

    void toDimacs(const char *file) { solver->write_dimacs(file); }
    void statistics() { solver->statistics(); }
};

}

class LitPropagator : public CaDiCaL::ExternalPropagator {
public:
    std::vector<int> last_trails[2];
    size_t dec_level;

    LitPropagator() : dec_level(0) { }

    ~LitPropagator () { };

    void notify_assignment (const std::vector<int>& lits) {
        for (int lit : lits) last_trails[dec_level % 2].push_back(lit);
    };
    void notify_new_decision_level () { 
        last_trails[++dec_level % 2].clear(); 
    };

    void notify_backtrack (size_t new_level) {
        if (new_level < dec_level) {
            last_trails[0].clear(); last_trails[1].clear();
            dec_level = new_level;
        }
    };

    bool cb_check_found_model (const std::vector<int> &) { return true; };

    bool cb_has_external_clause (bool& ) { return false; };

    int cb_add_external_clause_lit () { return 0; };
} ;


#endif
