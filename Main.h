/******************************************************************************************[Main.h]
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

#ifndef Main_h
#define Main_h

#include "Int.h"
#include "PbSolver.h"

#ifdef USE_SCIP
#include <mutex>
extern std::mutex stdout_mtx, optsol_mtx, fixed_vars_mtx;
#endif

//=================================================================================================


enum SolverT  { st_MiniSat, st_SatELite };
enum ConvertT { ct_Sorters, ct_Adders, ct_BDDs, ct_Mixed, ct_Undef };
enum Command  { cmd_Minimize, cmd_FirstSolution, cmd_AllSolutions };

// -- output options:
extern bool     opt_maxsat;
extern bool     opt_satlive;
extern bool     opt_ansi;
extern char*    opt_cnf;
extern int      opt_verbosity;
extern bool     opt_try;
extern int      opt_output_top;

// -- solver options:
extern ConvertT opt_convert;
extern ConvertT opt_convert_goal;
extern bool     opt_convert_weak;
extern double   opt_bdd_thres;
extern double   opt_sort_thres;
extern double   opt_goal_bias;
extern Int      opt_goal;
extern Command  opt_command;
extern bool     opt_branch_pbvars;
extern int      opt_polarity_sug;
extern bool     opt_shared_fmls;
extern int      opt_base_max;
extern int      opt_cpu_lim;
extern int      opt_minimization;
extern int      opt_seq_thres;
extern int      opt_bin_percent;
extern bool     opt_maxsat_msu;
extern double   opt_unsat_cpu;
extern bool     opt_lexicographic;
extern bool     opt_to_bin_search;
extern bool     opt_maxsat_prepr;
extern uint64_t opt_unsat_conflicts;

extern bool     opt_reuse_sorters;

// -- files:
extern char*    opt_input;
extern char*    opt_result;

// -- statistics;
extern unsigned long long int srtEncodings, addEncodings, bddEncodings;
extern unsigned long long int srtOptEncodings, addOptEncodings, bddOptEncodings;
 
//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

void reportf(const char* format, ...);      // 'printf()' replacer -- will put "c " first at each line if 'opt_satlive' is TRUE.
void outputResult(const PbSolver& S, bool optimum = true);


//=================================================================================================
#endif
