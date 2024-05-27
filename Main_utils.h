/*****************************************************************************************[Main.cc]

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

#ifndef MAIN_UTILS_H
#define MAIN_UTILS_H

#ifndef UWR_VERSION
#define UWR_VERSION "1.6.0"
#endif

extern bool   opt_model_out;
extern bool   opt_bin_model_out;
extern bool   opt_satisfiable_out;

extern bool   opt_preprocess;
extern bool   opt_old_format;
extern int    opt_mem_lim;
extern bool   opt_use_maxpre;
extern int    exit_code;

#ifdef MAXPRE
extern char   opt_maxpre_str[];
extern int    opt_maxpre_time;
extern int    opt_maxpre_skip;
#endif

#ifdef USE_SCIP
extern bool   opt_use_scip_slvr;
extern double opt_scip_cpu;
extern double opt_scip_cpu_default;
extern double opt_scip_cpu_add;
extern bool   opt_scip_parallel;
extern time_t wall_clock_time;
extern bool   opt_force_scip;
extern double opt_scip_delay;
#endif

extern MsSolver *pb_solver;

void reportf(const char* format, ...);
void SIGINT_handler(int /*signum*/);
void SIGTERM_handler(int signum);
void increase_stack_size(int new_size);
PbSolver::solve_Command convert(Command cmd);
void parseOptions(int argc, char** argv);
void setOptions(int argc, char** argv, bool check_files = true);

#endif
