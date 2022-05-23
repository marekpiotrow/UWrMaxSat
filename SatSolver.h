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

#ifndef SatSolver_h
#define SatSolver_h

#include "minisat/mtl/Vec.h"
#ifdef CADICAL
#include "CadicalWrap.h"
#elif defined(CRYPTOMS)
#include "CryptoMSWrap.h"
#else
#include "minisat/simp/SimpSolver.h"
#endif

#if defined(GLUCOSE3) || defined(GLUCOSE4)
namespace Minisat = Glucose;
#endif
#ifdef GLUCOSE4
#define rnd_decisions stats[14]
#define max_literals  stats[21]
#define tot_literals  stats[22]
#endif

#ifdef MAPLE
#define uncheckedEnqueue(p) uncheckedEnqueue(p,decisionLevel())
#endif

using Minisat::Var;
using Minisat::Lit;
using Minisat::SimpSolver;
using Minisat::lbool;
using Minisat::mkLit;
using Minisat::lit_Undef;
#ifdef MINISAT
using Minisat::l_Undef;
using Minisat::l_True;
using Minisat::l_False;
using Minisat::var_Undef;
#define VAR_UPOL l_Undef
#define LBOOL    lbool
#else
#define VAR_UPOL true
#define LBOOL
#endif

#ifdef BIG_WEIGHTS
using weight_t = Int; 
#define WEIGHT_MAX Int_MAX
#else
using weight_t = int64_t;
#define WEIGHT_MAX std::numeric_limits<weight_t>::max()
#endif

class ExtSimpSolver: public SimpSolver {
private:
    Minisat::vec<uint32_t> elimClauses;
public:
#if defined(COMINISATPS)
    ExtSimpSolver(bool print_info = true) { 
        if (print_info) printf("c Using COMiniSatPS SAT solver by Chanseok Oh (2016)\n"); }
#elif defined(MERGESAT)
    ExtSimpSolver(bool print_info = true) { use_ccnr = false; allow_rephasing = false; 
        if (print_info) printf("c Using MergeSat SAT solver by Norbert Manthey (2022)\n"); }
#elif defined(CADICAL)
    ExtSimpSolver(bool print_info = true) { 
        if (print_info) printf("c Using %s SAT solver by Armin Biere (2022)\n", solver->signature()); }
#elif defined(GLUCOSE4)
    ExtSimpSolver(bool print_info = true) { 
        if (print_info) printf("c Using Glucose 4.1 SAT solver by Gilles Audemard and Laurent Simon (2014)\n"); }
#endif
#if !defined(CADICAL) && !defined(CRYPTOMS)
    const Minisat::Clause& getClause  (int i, bool &is_satisfied) const;
#endif
    void reduceProblem();
    void extendGivenModel(vec<lbool> &model);
    void printVarsCls(bool encoding = true, const vec<Pair<weight_t, Minisat::vec<Lit>* > > *soft_cls = NULL, int soft_cls_sz = 0);
    // compute a list of propagated literals for a given literal lit under some possible global assumptions
    bool prop_check(Lit lit, Minisat::vec<Lit>& props, const vec<Lit>& assumptions, int psaving = 2);
};

#endif
