/*************************************************************************************[PbParser.cc]
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

#include "PbParser.h"
#include "File.h"
#include "Sort.h"
#ifdef MAXPRE
#include "preprocessorinterface.hpp"
#endif

//=================================================================================================
// Parser buffers (streams):


class FileBuffer {
    File    in;
    int     next;
public:
    int     line;
    FileBuffer(cchar* input_file) : in(input_file, "rb") {
        if (in.null()) reportf("ERROR! Could not open file for reading: %s\n", input_file), exit(0);
        next = in.getCharQ();
        line = 1; }
   ~FileBuffer() {}
    int  operator *  () { return next; }
    void operator ++ () { if (next == '\n') line++; next = in.getCharQ(); }
};


class StringBuffer {
    cchar*  ptr;
    cchar*  last;
public:
    int     line;
    StringBuffer(cchar* text)           { ptr = text; last = ptr + strlen(text); line = 1; }
    StringBuffer(cchar* text, int size) { ptr = text; last = ptr + size; line = 1; }
   ~StringBuffer() {}
    int  operator *  () { return (ptr >= last) ? EOF : *ptr; }
    void operator ++ () { if (*ptr == '\n') line++; ++ptr; }
};



//=================================================================================================
// PB Parser:


/*
The 'B' (parser Buffer) parameter should implement:
    
    operator *      -- Peek at current token. Should return a character 0-255 or 'EOF'.
    operator ++     -- Advance to next token.
    line            -- Public member variable.

The 'S' (Solver) parameter should implement:

    void allocConstrs(int n_vars, int n_constrs)
        -- Called before any of the below methods. Sets the size of the problem.

    int  getVar(cchar* name)
        -- Called during parsing to convert string names to indices. Ownership of 'name' 
        remains with caller (the string should be copied).

    void addGoal(const vec<Lit>& ps, const vec<Int>& Cs)
        -- Called before any constraint is adde to establish goal function:
                "minimize( Cs[0]*ps[0] + ... + Cs[n-1]*ps[n-1] )"

    bool addConstr(const vec<Lit>& ps, const vec<Int>& Cs, Int rhs, int ineq)
        -- Called when a constraint has been parsed. Constraint is of type:
                "Cs[0]*ps[0] + ... + Cs[n-1]*ps[n-1] >= rhs" ('rhs'=right-hand side). 
        'ineq' determines the inequality used: -2 for <, -1 for <=, 0 for ==, 1 for >=, 2 for >. 
        Should return TRUE if successful, FALSE if conflict detected.
*/


template<class B>
static void skipWhitespace(B& in) {     // not including newline
    while (*in == ' ' || *in == '\t' || *in == '\r')
        ++in; }

template<class B>
static void skipLine(B& in) {
    for (;;){
        if (*in == EOF) return;
        if (*in == '\n') { ++in; return; }
        ++in; } }

template<class B>
static void skipComments(B& in) {      // skip comment and empty lines (assuming we are at beginning of line)
    char start = (opt_maxsat ? 'c' : '*');
    while (*in == start || *in == '\n') skipLine(in); }

template<class B>
static bool skipEndOfLine(B& in) {     // skip newline AND trailing comment/empty lines
    skipWhitespace(in);
    if (*in == '\n') ++in;
    else             return false;
    skipComments(in);
    return true; }

template<class B>
static bool skipText(B& in, cchar* text) {
    while (*text != 0){
        if (*in != *text) return false;
        ++in, ++text; }
    return true; }

template<class B>
static Int parseInt(B& in) {
    Int     val(0);
    bool    neg = false;
    skipWhitespace(in);
    if      (*in == '-') neg = true, ++in;
    else if (*in == '+') ++in;
    skipWhitespace(in);     // BE NICE: allow "- 3" and "+  4" etc.
    if (*in < '0' || *in > '9')
        throw nsprintf("Expected digit, not: %c", *in);
    while (*in >= '0' && *in <= '9'){
      #ifdef NO_GMP
        val *= 2;
        if (val < 0 || val > Int(9223372036854775807LL >> 20)) throw xstrdup("Integer overflow. Use BigNum-version.");      // (20 extra bits should be enough...)
        val *= 5;
      #else
        val *= 10;
      #endif
        val += (*in - '0');
        ++in; }
    return neg ? -val : val; }

template<class B>
static char* parseIdent(B& in, vec<char>& tmp) {   // 'tmp' is cleared, then filled with the parsed string. '(char*)tmp' is returned for convenience.
    skipWhitespace(in);
    if ((*in < 'a' || *in > 'z') && (*in < 'A' || *in > 'Z') && *in != '_') throw nsprintf("Expected start of identifier, not: %c", *in);
    tmp.clear();
    tmp.push(*in);
    ++in;
    while ((*in >= 'a' && *in <= 'z') || (*in >= 'A' && *in <= 'Z') || (*in >= '0' && *in <= '9') || *in == '_')
        tmp.push(*in),
        ++in;
    tmp.push(0);
    return (char*)tmp; }


template<class B, class S>
void parseExpr(B& in, S& solver, vec<Lit>& out_ps, vec<Int>& out_Cs, vec<char>& tmp, bool old_format)
    // NOTE! only uses "getVar()" method of solver; doesn't add anything.
    // 'tmp' is a tempory, passed to avoid frequent memory reallocation.
{
    bool empty = true;
    for(;;){
        skipWhitespace(in);
        if ((*in < '0' || *in > '9') && *in != '+' && *in != '-') break;
        out_Cs.push(parseInt(in));
        skipWhitespace(in);
        if (old_format){
            if (*in != '*') throw xstrdup("Missing '*' after coefficient.");
            ++in; }
        out_ps.push(mkLit(solver.getVar(parseIdent(in, tmp))));
        empty = false;
    }
    if (empty) throw xstrdup("Empty expression.");
}


template<class B, class S>
void parseSize(B& in, S& solver)
{
    int n_vars, n_constrs;

    if (*in != '*') return;
    ++in;
    skipWhitespace(in);

    if (!skipText(in, "#variable=")) goto Abort;
    n_vars = toint(parseInt(in));

    skipWhitespace(in);
    if (!skipText(in, "#constraint=")) goto Abort;
    n_constrs = toint(parseInt(in));

    solver.allocConstrs(n_vars, n_constrs);

  Abort:
    skipLine(in);
    skipComments(in);
}

template<class B, class S>
void parseGoal(B& in, S& solver, bool old_format)
{
    skipWhitespace(in);
    if (!skipText(in, "min:")) return;      // No goal specified. If file is syntactically correct, no characters will have been consumed (expecting integer).

    vec<Lit> ps; vec<Int> Cs; vec<char> tmp;
    skipWhitespace(in);
    if (*in == '\n') skipLine(in);
    if (*in == ';'){
        ++in;
        skipLine(in);
    }else{
        parseExpr(in, solver, ps, Cs, tmp, old_format);
        skipWhitespace(in);
        if (!skipText(in, ";")) throw xstrdup("Expecting ';' after goal function.");
    }
    skipEndOfLine(in);

    solver.addGoal(ps, Cs);
}

template<class B>
int parseInequality(B& in)
{
    int ineq;
    skipWhitespace(in);
    if (*in == '<'){
        ++in;
        if (*in == '=') ineq = -1, ++in;
        else            ineq = -2;
    }else if (*in == '>'){
        ++in;
        if (*in == '=') ineq = +1, ++in;
        else            ineq = +2;
    }else{
        if (*in == '='){
            ++in;
            if (*in == '=') ++in;
            ineq = 0;
        }else
            throw nsprintf("Expected inequality, not: %c", *in);
    }
    return ineq;
}

template<class B, class S>
bool parseConstrs(B& in, S& solver, bool old_format)
{
    vec<Lit> ps; vec<Int> Cs; vec<char> tmp;
    int     ineq;
    Int     rhs;
    while (*in != EOF){
        parseExpr(in, solver, ps, Cs, tmp, old_format);
        ineq = parseInequality(in);
        rhs  = parseInt(in);

        skipWhitespace(in);
        if (!skipText(in, ";")) throw xstrdup("Expecting ';' after constraint.");
        skipEndOfLine(in);

        Lit lit = lit_Undef;
        if (!solver.addConstr(ps, Cs, rhs, ineq, lit))
            return false;
        ps.clear();
        Cs.clear();
    }
    return true;
}

template<class B, class S>
static void parse_p_line(B& in, S& solver, bool& wcnf_format, Int& hard_bound)
{
    extern bool opt_use_maxpre;
    int n_vars, n_constrs;
    vec<char> tmp(15,0);

    skipComments(in);

    if (*in != 'p') return;
    ++in;
    skipWhitespace(in);

    if (!skipText(in, "wcnf")) {
        wcnf_format = false;
        if (!skipText(in, "cnf")) goto Abort;
    }
    n_vars = toint(parseInt(in));

    n_constrs = toint(parseInt(in));

    if (opt_use_maxpre && n_constrs >= 1000000) {
        opt_use_maxpre = false;
        reportf("MaxPre switched off due to a huge number of constraints (>1000000)\n");
    }

    skipWhitespace(in);
    if (*in >= '0' && *in <= '9' || *in == '+') 
        hard_bound = parseInt(in);

    if (!opt_use_maxpre) {
        solver.allocConstrs(n_vars, n_constrs);
        for (int i = 1; i <= n_vars; i++) {
            sprintf(&tmp[0], "%d", i);
            solver.getVar(tmp);
        }
    }
  Abort:
    skipLine(in);
    skipComments(in);
}

template<class B>
static bool parseLit(B& in, vec<char>& tmp) {   // 'tmp' is cleared, then filled with the parsed string.
    bool negated = false;
    skipWhitespace(in);
    if (*in == '-') negated = true, ++in;
    if (*in < '0' || *in > '9') throw nsprintf("Expected start of var number, not: %c(%d)", *in, *in);
    tmp.clear();
    tmp.push(*in);
    ++in;
    while (*in >= '0' && *in <= '9') tmp.push(*in), ++in;
    tmp.push(0);
    return negated; }

template<class B, class S>
static bool parse_wcnfs(B& in, S& solver, bool wcnf_format, Int hard_bound)
{
    vec<Lit> ps, gps; vec<Int> gCs; vec<char> tmp;
    int    gvars = 0;
    Int one(1), weight(0);
    int n_vars = 0, n_constrs = 0;

#ifdef MAXPRE
    extern bool opt_use_maxpre;
    extern char opt_maxpre_str[80];
    extern int  opt_maxpre_time;
    extern int  opt_maxpre_skip;
    extern maxPreprocessor::PreprocessorInterface *maxpre_ptr;
    std::vector<std::vector<int> > clauses;
    std::vector<uint64_t>  weights;
    Int weight_sum(0);
#endif

    tmp.clear(); tmp.growTo(15,0);
    while (*in != EOF){
        skipWhitespace(in);
        if (*in == 'h') ++in, weight = hard_bound;
        else
            weight = (wcnf_format ? parseInt(in) : Int(1));
#ifdef MAXPRE
        if (opt_use_maxpre) clauses.push_back(std::vector<int>());
#endif
        while (1) {
            bool negated = parseLit(in,tmp);
            if (tmp.size() == 2 && tmp[0] == '0') break;
            int v = atoi(&tmp[0]);
#ifdef MAXPRE
            if (opt_use_maxpre) clauses.back().push_back(negated ? -v : v), ps.push(mkLit(v, negated));
            else
#endif
            {
                if (solver.declared_n_vars < 0) {
                    vec<char> t(15,0);
                    while (n_vars < v) { sprintf(&t[0], "%d", ++n_vars); solver.getVar(t); }
                }
                ps.push(mkLit(solver.getVar(tmp), negated));
            }
        }
        skipEndOfLine(in);
#ifdef MAXPRE
        if (opt_use_maxpre) {
            if (weight <= 0) { clauses.pop_back(); ps.clear(); continue; }
            weights.push_back(weight >= hard_bound ? 0 : tolong(weight));
            if (weight < hard_bound) {
                solver.storeSoftClause(ps, tolong(weight));
                weight_sum += weight;
            }
        } else 
#endif
        if (weight <= 0) { ps.clear(); continue; }
        else if (weight >= hard_bound) {
            if (!solver.addClause(ps)) return false;
        } else {
            if (ps.size() == 1) {
                if (!opt_maxsat_msu) gps.push(~ps.last()), gCs.push(weight);
            } else {
                ps.push(lit_Undef);
                if (!opt_maxsat_msu) gps.push(ps.last()), gCs.push(weight);
            }
#ifdef BIG_WEIGHTS
            solver.storeSoftClause(ps, weight);
#else
            solver.storeSoftClause(ps, tolong(weight));
#endif
        }
        if (solver.declared_n_constrs < 0 && ps.size() > 0) n_constrs++;
        ps.clear();
    }
#ifdef MAXPRE
    if (!opt_use_maxpre)
#endif
    {
        if (solver.declared_n_vars < 0 && n_vars > 0) solver.declared_n_vars = n_vars;
        if (solver.declared_n_constrs < 0 && n_constrs > 0) solver.declared_n_constrs = n_constrs;
        gvars = solver.soft_cls.size();
        tmp.clear(); tmp.growTo(16,0);
        for (int i = 0; i < gvars; i++)
            if (solver.soft_cls[i].snd->last() == lit_Undef) {
                sprintf(&tmp[0],"#%d",i + 1);
                Lit p = mkLit(solver.getVar(tmp), true);
                solver.soft_cls[i].snd->last() = p;
                if (!opt_maxsat_msu) gps[i] = p;
            }
    }
#ifdef MAXPRE
    if (opt_use_maxpre) {
        reportf("Using MaxPre - an MaxSAT preprocessor by Tuukka Korhonen (2017) with techniques: %s\n", 
                opt_maxpre_str);
        if (++weight_sum < hard_bound) hard_bound = weight_sum;
        uint64_t topWeight = tolong(hard_bound);
        for (auto &w : weights) 
            if (w == 0 || w > topWeight) w = topWeight;
        maxpre_ptr = new maxPreprocessor::PreprocessorInterface(clauses, weights, topWeight);
        if (opt_maxpre_skip >= 10) maxpre_ptr->setSkipTechnique(opt_maxpre_skip);
        if (opt_maxpre_time > 0)   maxpre_ptr->preprocess(std::string(opt_maxpre_str), 0, opt_maxpre_time);
        else                       maxpre_ptr->preprocess(std::string(opt_maxpre_str));
        if (opt_verbosity > 0) maxpre_ptr->printTimeLog(std::cout);
        solver.soft_cls.moveTo(solver.orig_soft_cls);
        solver.soft_cls.clear(); clauses.clear(); weights.clear();
        std::vector<int> labels;
        maxpre_ptr->getInstance(clauses, weights, labels);
        assert(clauses.size() == weights.size());
        tmp.clear(); tmp.growTo(15,0);
        for (unsigned maxvar = 1, i = 0 ; i < clauses.size(); i++) {
            ps.clear(); 
            for (unsigned j = 0; j < clauses[i].size(); j++) {
                unsigned var = abs(clauses[i][j]);
                for ( ; maxvar <= var; maxvar++) {
                    sprintf(&tmp[0],"%d",maxvar);
                    solver.getVar(tmp);
                }
                ps.push(mkLit(var - 1, clauses[i][j] < 0));
            }
            if (weights[i] == 0) continue;
            if (weights[i] >= topWeight) {
                if (!solver.addClause(ps)) return false;
            } else {
                if (!opt_maxsat_msu) 
                    gps.push(ps.size() == 1 ? ~ps.last() : ps.last()), gCs.push((int64_t)weights[i]);
                solver.storeSoftClause(ps, (int64_t)weights[i]);
            }
        }
        if (clauses.size() == 0) {
            solver.getVar("1");
            ps.clear();
            ps.push(mkLit(0, false)); ps.push(mkLit(0, true)); solver.addClause(ps);
            ps.pop(); solver.storeSoftClause(ps,1);
            if (!opt_maxsat_msu) gps.push(mkLit(0,true)), gCs.push(1);
        } else
            clauses.clear(), weights.clear();
    }
#endif
    if (gvars == 0 && !opt_maxsat_msu) {
        tmp.clear(); tmp.growTo(10,0);
        sprintf(&tmp[0],"#%d",1);
        gps.push(mkLit(solver.getVar(tmp)));
        gCs.push(one);
    }
    if (!opt_maxsat_msu) solver.addGoal(gps, gCs);
    return true;
}


//=================================================================================================
// Main parser functions:


template<class B, class S>
static bool parse_PB(B& in, S& solver, bool old_format, bool abort_on_error)
{
    try{
        parseSize(in, solver);
        parseGoal(in, solver, old_format);
        return parseConstrs(in, solver, old_format);
    }catch (cchar* msg){
        if (abort_on_error){
            reportf("PARSE ERROR! [line %d] %s\n", in.line, msg);
            xfree(msg);
            if (opt_satlive && !opt_try)
                printf("s UNKNOWN\n");
            exit(5);
        }else
            throw msg;
    }

}

// PB parser functions: Returns TRUE if successful, FALSE if conflict detected during parsing.
// If 'abort_on_error' is false, a 'cchar*' error message may be thrown.
//
void parse_PB_file(cchar* filename, PbSolver& solver, bool old_format, bool abort_on_error) {
    FileBuffer buf(filename);
    parse_PB(buf, solver, old_format, abort_on_error); }

// WCNF parse functions
//
template<class B, class S>
static bool parse_WCNF(B& in, S& solver, bool abort_on_error)
{
    Int hard_bound = WEIGHT_MAX;
    bool wcnf_format = true;

    try{
        parse_p_line(in, solver, wcnf_format, hard_bound);
        return parse_wcnfs(in, solver, wcnf_format, hard_bound);
    }catch (cchar* msg){
        if (abort_on_error){
            reportf("PARSE ERROR! [line %d] %s\n", in.line, msg);
            xfree(msg);
            if (opt_satlive && !opt_try)
                printf("s UNKNOWN\n");
            exit(5);
        }else
            throw msg;
    }

}

void parse_WCNF_file(cchar* filename, MsSolver& solver, bool abort_on_error) {
    FileBuffer buf(filename);
    parse_WCNF(buf, solver, abort_on_error); }

//=================================================================================================
// Debug:


#if 0
#include "Debug.h"
#include "Map.h"
#define Solver DummySolver

struct DummySolver {
    Map<cchar*, int> name2index;
    vec<cchar*>      index2name;

    int getVar(cchar* name) {
        int ret;
        if (!name2index.peek(name, ret)){
            index2name.push(xstrdup(name));
            ret = name2index.set(index2name.last(), index2name.size()-1); }
        return ret; }

    void alloc(int n_vars, int n_constrs) {
        printf("alloc(%d, %d)\n", n_vars, n_constrs); }
    void addGoal(vec<Lit>& ps, vec<Int>& Cs) {
        printf("MIN: "); dump(ps, Cs); printf("\n"); }
    bool addConstr(vec<Lit>& ps, vec<Int>& Cs, Int rhs, int ineq) {
        static cchar* ineq_name[5] = { "<", "<=" ,"==", ">=", ">" };
        printf("CONSTR: "); dump(ps, Cs); printf(" %s ", ineq_name[ineq+2]); dump(rhs); printf("\n");
        return true; }
};

void test(void)
{
    DummySolver     solver;
    debug_names = &solver.index2name;
    parseFile_PB("test.pb", solver, true);
}
#endif
