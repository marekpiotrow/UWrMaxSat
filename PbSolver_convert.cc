/*****************************************************************************[PbSolver_convert.cc]
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

#include "PbSolver.h"
#include "Hardware.h"
//#include "Sort.h"
#include<algorithm>
//-------------------------------------------------------------------------------------------------
void    linearAddition (const Linear& c, vec<Formula>& out);        // From: PbSolver_convertAdd.C
Formula buildConstraint(const Linear& c, int max_cost = INT_MAX);   // From: PbSolver_convertSort.C
Formula convertToBdd   (const Linear& c, int max_cost = INT_MAX);   // From: PbSolver_convertBdd.C
//-------------------------------------------------------------------------------------------------

bool cmpLT(Linear *p, Linear *q) { return p != NULL && (q == NULL || p->size < q->size); }

bool PbSolver::convertPbs(bool first_call)
{
    vec<Formula>    converted_constrs;
    ConvertT saved_opt_convert = opt_convert;
    int nvars = sat_solver.nVars(), ncls = sat_solver.nClauses();

    if (first_call){
        if (!opt_maxsat) findIntervals();
        if (!rewriteAlmostClauses()) {
            sat_solver.addEmptyClause();
            return false;
        }
        extern bool opt_reuse_sorters;
        if (opt_reuse_sorters)
            std::stable_sort(&constrs[0], &constrs[0]+constrs.size(), cmpLT);
    }

    for (int i = 0; i < constrs.size(); i++) {
        if (constrs[i] == NULL) continue;
        Linear& c   = *constrs[i]; assert(c.lo != Int_MIN || c.hi != Int_MAX);

        if (opt_verbosity >= 1) 
            if (first_call && !opt_maxsat) /**/ reportf("---[%4d]---> ", constrs.size() - 1 - i); 
        try {
            if (opt_convert == ct_Sorters)
                converted_constrs.push(buildConstraint(c)), first_call ? ++srtEncodings : ++srtOptEncodings;
            else if (opt_convert == ct_Adders)
                linearAddition(c, converted_constrs), first_call ? ++addEncodings : ++addOptEncodings;
            else if (opt_convert == ct_BDDs)
                converted_constrs.push(convertToBdd(c)), first_call ? ++bddEncodings : ++bddOptEncodings;
            else if (opt_convert == ct_Mixed) {
                int adder_cost = estimatedAdderCost(c);
                Formula result = buildConstraint(c, (int)(adder_cost * opt_sort_thres)); 
                if (result == _undef_) {
                    result = convertToBdd(c, (int)(adder_cost * opt_bdd_thres));
                    if (result != _undef_)
                        if (!first_call) opt_convert = ct_BDDs, ++bddOptEncodings; else ++bddEncodings; 
                } else if (!first_call) opt_convert = ct_Sorters, ++srtOptEncodings; else ++srtEncodings;
                if (result == _undef_) linearAddition(c, converted_constrs), first_call ? ++addEncodings : ++addOptEncodings;
                else converted_constrs.push(result);
            } else assert(false);
            if (first_call || !(opt_maxsat_msu && opt_shared_fmls && opt_minimization == 1))
                constrs[i]->~Linear(), constrs[i] = NULL;
            if (!opt_shared_fmls && FEnv::nodes.size() >= 100000) { 
                clausify(sat_solver, converted_constrs); converted_constrs.clear();
            }
            opt_convert = saved_opt_convert;
        } catch (std::bad_alloc& ba) {
	    FEnv::pop(); i-=1;
	    if (opt_convert == ct_Sorters)  { opt_convert = ct_BDDs; continue; }
	    if (opt_convert != ct_Adders)  { opt_convert = ct_Adders; continue; }
            else {
	        reportf("Out of memery in converting constraints: %s\n",ba.what());
	        exit(1);
	    }
        }
        if (!okay()) return false;
    }

    try {
        if (first_call || !(opt_maxsat_msu && opt_shared_fmls && opt_minimization == 1)) {
            constrs.clear(), mem.clear();
            clausify(sat_solver, converted_constrs);
        } else {
            vec<Lit> out;
            clausify(sat_solver, converted_constrs, out);
            for (int i = 0, j = 0; i < constrs.size(); i++) 
                if (constrs[i] != NULL) constrs[i]->lit = out[j++];
        }
        if (opt_verbosity >=2 && ((nvars -= sat_solver.nVars()) < 0 | (ncls -= sat_solver.nClauses()) < 0)) 
            reportf("New vars/cls: %d/%d\n", -nvars, -ncls);
    } catch (std::bad_alloc& ba) {
      reportf("Out of memery in clausifying constraints: %s\n",ba.what());
      exit(1);
    }
    return okay();
}
