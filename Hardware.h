/**************************************************************************************[Hardware.h]
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

#ifndef Hardware_h
#define Hardware_h

#include "PbSolver.h"
#include "FEnv.h"

//=================================================================================================


int  estimatedAdderCost(const Linear& c);
int  encodeBySorter(vec<Formula>& fs, int max_sel, int ineq, bool soft_constr);
void keepLastSequences(void);
void removeLastSequences(void);
void encodeByMerger(const vec<Formula>& in1,  const vec<Formula>& in2, vec<Formula>& outvars, unsigned k, int ineq);
void rippleAdder(const vec<Formula>& xs, const vec<Formula>& ys, vec<Formula>& out);
void addPb(const vec<Formula>& ps, const vec<Int>& Cs_, vec<Formula>& out, int bits);

void clausify(SimpSolver& s, const vec<Formula>& fs, vec<Lit>& out);
void clausify(SimpSolver& s, const vec<Formula>& fs);


//=================================================================================================
#endif
