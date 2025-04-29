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

#ifndef SatSolver_h
#define SatSolver_h

#include "minisat/mtl/Vec.h"
#ifdef CADICAL
#include "CadicalWrap.h"
namespace Minisat = COMinisatPS;
#elif defined(CRYPTOMS)
#include "CryptoMSWrap.h"
namespace Minisat = COMinisatPS;
#else
#include "minisat/simp/SimpSolver.h"
#endif

#if defined(GLUCOSE3) || defined(GLUCOSE4)
namespace Minisat = Glucose;
#elif defined(COMINISATPS)
namespace Minisat = COMinisatPS;
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
#if defined(CADICAL)
    LitPropagator *extPropagator;
#endif
public:
    ExtSimpSolver(bool print_info = true)
#if defined(CADICAL)
        : extPropagator(nullptr) 
#endif
    { 
        if (print_info) printf(
#if defined(COMINISATPS)
        "c Using COMiniSatPS SAT solver by Chanseok Oh (2016)\n"
#elif defined(MERGESAT)
        "c Using MergeSat SAT solver by Norbert Manthey (2022)\n"
#elif defined(CADICAL)
        "c Using %s SAT solver by Armin Biere (2022)\n", solver->signature()
#elif defined(GLUCOSE4)
        "c Using Glucose 4.1 SAT solver by Gilles Audemard and Laurent Simon (2014)\n"
#elif defined(CRYPTOMS)
        "c Using CryptoMiniSat (ver. 5.8.0) SAT solver by its Authors (2020)\n"
#elif defined(MINISAT)
        "c Using MiniSat (ver. 2.2.0) SAT solver by Niklas Een and Niklas Sorensson (2010)\n"
#endif
        );
    }
#if !defined(CADICAL) && !defined(CRYPTOMS)
    const Minisat::Clause& getClause  (int i, bool &is_satisfied) const;
#endif
    bool reduceProblem(int level = 0);
    void extendGivenModel(vec<lbool> &model);
    void optimizeModel(const vec<Pair<weight_t, Minisat::vec<Lit>* > >& soft_cls, vec<bool>& model, int from_soft, int to_soft);
    void printVarsCls(bool encoding = true, const vec<Pair<weight_t, Minisat::vec<Lit>* > > *soft_cls = NULL, int soft_cls_sz = 0);
    void startPropagator(const Minisat::vec<Lit>& observed); // needed in CaDiCaL
    void stopPropagator(); // needed in CaDiCaL
    // compute a list of propagated literals for a given literal lit under some possible global assumptions
    bool impliedObservedLits(Lit lit, Minisat::vec<Lit>& props, const vec<Lit>& assumptions, int psaving = 2);
};

#endif
