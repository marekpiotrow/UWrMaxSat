/*****************************************************************************************[Main.cc]

Minisat+ -- Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson

KP-MiniSat+ based on MiniSat+ -- Copyright (c) 2018-2020 Michał Karpiński, Marek Piotrów

UWrMaxSat based on KP-MiniSat+ -- Copyright (c) 2019-2021 Marek Piotrów

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

/**************************************************************************************************

Read a DIMACS file and apply the SAT-solver to it.

**************************************************************************************************/


#include <unistd.h>
#include <signal.h>
#include "System.h"
#include "MsSolver.h"
#include "PbParser.h"
#include "FEnv.h"

#ifdef MAXPRE
#include "preprocessorinterface.hpp"
#endif

#ifdef USE_SCIP
#include <mutex>
std::mutex stdout_mtx, optsol_mtx;
#endif

//=================================================================================================
// Command line options:

bool     opt_maxsat    = false;
bool     opt_satlive   = true;
bool     opt_ansi      = true;
char*    opt_cnf       = NULL;
int      opt_verbosity = 1;
bool     opt_model_out = true;
bool     opt_bin_model_out = false;
bool     opt_satisfiable_out = true;
bool     opt_try       = false;     // (hidden option -- if set, then "try" to parse, but don't output "s UNKNOWN" if you fail, instead exit with error code 5)
int      opt_output_top    = -1;

bool     opt_preprocess    = true;
ConvertT opt_convert       = ct_Undef;
ConvertT opt_convert_goal  = ct_Undef;
bool     opt_convert_weak  = true;
double   opt_bdd_thres     = 10;
double   opt_sort_thres    = 200;
double   opt_goal_bias     = 10;
Int      opt_goal          = Int_MAX;
Command  opt_command       = cmd_Minimize;
bool     opt_branch_pbvars = false;
int      opt_polarity_sug  = 1;
bool     opt_old_format    = false;
bool     opt_shared_fmls   = false;
int      opt_base_max      = 47;
int      opt_cpu_lim       = INT32_MAX;
int      opt_mem_lim       = INT32_MAX;

int      opt_minimization  = -1; // -1 = to be set, 0 = sequential. 1 = alternating, 2 - binary
int      opt_seq_thres     = -1; // -1 = to be set, 3 = maxsat default, 96 = PB default
int      opt_bin_percent   = 65;
bool     opt_maxsat_msu    = true;
double   opt_unsat_cpu     = 50; // in seconds
bool     opt_lexicographic = false;
bool     opt_to_bin_search = true;
bool     opt_maxsat_prepr  = true;
bool     opt_use_maxpre    = false;
bool     opt_reuse_sorters = true;
uint64_t opt_unsat_conflicts = 5000000;
#ifdef MAXPRE
char     opt_maxpre_str[80]= "[bu]#[buvsrgc]";
int      opt_maxpre_time   = 0;
int      opt_maxpre_skip   = 0;
maxPreprocessor::PreprocessorInterface *maxpre_ptr = NULL;
#endif

#ifdef USE_SCIP
bool     opt_use_scip_slvr = true;
double   opt_scip_cpu      = 0;
double   opt_scip_cpu_default = 400;
bool     opt_scip_parallel = true;
time_t   wall_clock_time;
#endif

char*    opt_input  = NULL;
char*    opt_result = NULL;

// -- statistics;
unsigned long long int srtEncodings = 0, addEncodings = 0, bddEncodings = 0;
unsigned long long int srtOptEncodings = 0, addOptEncodings = 0, bddOptEncodings = 0;

//- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -


void reportf(const char* format, ...)
{
#ifdef USE_SCIP
    std::lock_guard<std::mutex> lck(stdout_mtx);
#endif
    static bool col0 = true;
    static bool bold = false;
    va_list args;
    va_start(args, format);
    char* text = vnsprintf(format, args);
    va_end(args);

    if (col0 && text[0] == '\n' && !text[1]) { fflush(stdout); return; }
    for(char* p = text; *p != 0; p++){
        if (col0 && opt_satlive)
            putchar('c'), putchar(' ');

        if (*p == '\b'){
            bold = !bold;
            if (opt_ansi)
                putchar(27), putchar('['), putchar(bold?'1':'0'), putchar('m');
            col0 = false;
        }else{
            putchar(*p);
            col0 = (*p == '\n' || *p == '\r');
        }
    }
    fflush(stdout);
}


//=================================================================================================
// Helpers:


MsSolver*   pb_solver = NULL;   // Made global so that the SIGTERM handler can output best solution found.
static bool resultsPrinted = false;

void outputResult(const PbSolver& S, bool optimum)
{
#ifdef USE_SCIP
    std::lock_guard<std::mutex> lck(stdout_mtx);
#endif
    if (!opt_satlive || resultsPrinted) return;

    if (opt_model_out && S.best_goalvalue != Int_MAX){
#ifdef MAXPRE
        if (opt_use_maxpre) {
            std::vector<int> trueLiterals, model;
            for (int i = 0; i < S.best_model.size(); i++)
                trueLiterals.push_back(S.best_model[i] ? i+1 : -i-1);
            model = maxpre_ptr->reconstruct(trueLiterals);
            if (!optimum) {
                Int sum = 0;
                vec<bool> bmodel( abs(model.back()) + 1);
                for (int i = model.size() - 1; i >= 0; i--) bmodel[abs(model[i])] = (model[i] > 0);
                for (int j, i = pb_solver->orig_soft_cls.size() - 1; i >= 0; i--) {
                    for (j = pb_solver->orig_soft_cls[i].snd->size() - 1; j >= 0; j--) {
                        Lit p = (*pb_solver->orig_soft_cls[i].snd)[j];
                        if ((sign(p) && !bmodel[var(p)]) || (!sign(p) && bmodel[var(p)])) break;
                    }
                    if (j < 0) sum += pb_solver->orig_soft_cls[i].fst;
                }
                if (sum < S.best_goalvalue) printf("o %s\n", toString(sum));
            }
            if (opt_bin_model_out) {
                printf("v ");
                for (int i = 0; i < (int)model.size(); i++) {
                    assert(model[i] == i+1 || model[i] == -i-1);
                    putchar(model[i] < 0 ? '0' : '1');
                }
            } else {
                printf("v");
                for (unsigned i = 0; i < model.size(); i++)
                    printf(" %d", model[i]);
            }
        } else
#endif
        if (optimum || opt_satisfiable_out) {
            if (opt_bin_model_out) {
                printf("v ");
                for (int i = 0; i < S.declared_n_vars; i++)
                    putchar(S.best_model[i]? '1' : '0');
            } else {
                printf("v");
                for (int i = 0; i < S.best_model.size(); i++)
                    if (S.index2name[i][0] != '#')
                        printf(" %s%s", S.best_model[i]?"":"-", S.index2name[i]);
            }
        }
        printf("\n");
    }
    if (opt_output_top < 0) {
        if (optimum){
            if (S.best_goalvalue == Int_MAX) printf("s UNSATISFIABLE\n");
            else {
                if (!opt_satisfiable_out) {
                    char* tmp = toString(S.best_goalvalue);
                    printf("o %s\n", tmp);
                    xfree(tmp);
                }
                printf("s OPTIMUM FOUND\n");
            }
        }else{
            if (S.best_goalvalue == Int_MAX) printf("s UNKNOWN\n");
            else                             printf("%c SATISFIABLE\n", (opt_satisfiable_out ? 's' : 'c'));
        }
        resultsPrinted = true;
    } else if (opt_output_top == 1) resultsPrinted = true;
    fflush(stdout);
}

void handlerOutputResult(const PbSolver& S, bool optimum = true)
{     // Signal handler save version of the function outputResult
    constexpr int BUF_SIZE = 50000;
    static char buf[BUF_SIZE];
    static int lst = 0;
    if (!opt_satlive || resultsPrinted || opt_output_top >= 0) return;
    if (opt_model_out && S.best_goalvalue != Int_MAX){
#ifdef MAXPRE
        if (opt_use_maxpre) {
            std::vector<int> trueLiterals, model;
            for (int i = 0; i < S.best_model.size(); i++)
                trueLiterals.push_back(S.best_model[i] ? i+1 : -i-1);
            model = maxpre_ptr->reconstruct(trueLiterals);
            vec<bool> bmodel( abs(model.back()) + 1);
            for (int i = model.size() - 1; i >= 0; i--) bmodel[abs(model[i])] = (model[i] > 0);
            if (!optimum && opt_satisfiable_out) {
                Int sum = 0;
                for (int j, i = pb_solver->orig_soft_cls.size() - 1; i >= 0; i--) {
                    for (j = pb_solver->orig_soft_cls[i].snd->size() - 1; j >= 0; j--) {
                        Lit p = (*pb_solver->orig_soft_cls[i].snd)[j];
                        if ((sign(p) && !bmodel[var(p)]) || (!sign(p) && bmodel[var(p)])) break;
                    }
                    if (j < 0) sum += pb_solver->orig_soft_cls[i].fst;
                }
                if (sum < pb_solver->best_goalvalue * pb_solver->goal_gcd) {
                    buf[lst++] = '\n'; buf[lst++] = 'o'; buf[lst++] = ' ';
                    if (sum == 0) buf[lst++] =  '0';
                    else {
                        char *first = buf + lst;
                        while (sum > 0) buf[lst++] = '0' + toint(sum%10), sum /= 10;
                        for (char *last = buf+lst-1; first < last; first++, last--) { 
                            char c = *first; *first = *last; *last = c; }
                    }
                }
            }
            if (optimum || opt_satisfiable_out) {
                buf[lst++] = '\n'; buf[lst++] = 'v';
                if (opt_bin_model_out) {
                    buf[lst++] = ' ';
                    for (int i = 1; i < bmodel.size(); i++) {
                        if (lst + 3 >= BUF_SIZE) { 
                            buf[lst++] = '\n'; lst = write(1, buf, lst); buf[0] = 'v'; buf[1] = ' '; lst = 2; 
                        }
                        buf[lst++] = (bmodel[i]? '1' : '0');
                    }
                } else
                    for (unsigned i = 0; i < model.size(); i++) {
                        if (lst + 15 >= BUF_SIZE) { 
                            buf[lst++] = '\n'; lst = write(1, buf, lst); buf[0] = 'v'; lst = 1; 
                        }
                        buf[lst++] = ' ';
                        if (model[i] < 0) { buf[lst++] = '-'; model[i] = -model[i]; }
                        char *first = buf + lst;
                        for (int v = model[i]; v > 0; v /= 10) buf[lst++] = '0' + v%10;
                        for (char *last = buf+lst-1; first < last; first++, last--) { 
                            char c = *first; *first = *last; *last = c; }
                    }
            }
        } else
#endif
        if (optimum || opt_satisfiable_out) {
            buf[0] = '\n'; buf[1] = 'v'; lst += 2;
            if (opt_bin_model_out) {
                buf[lst++] = ' ';
                for (int i = 0; i < S.declared_n_vars; i++) {
                    if (lst + 3 >= BUF_SIZE) { 
                        buf[lst++] = '\n'; lst = write(1, buf, lst); buf[0] = 'v'; buf[1] = ' '; lst = 2; 
                    }
                    buf[lst++] = (S.best_model[i]? '1' : '0');
                }
            } else
                for (int i = 0; i < S.best_model.size(); i++)
                    if (S.index2name[i][0] != '#') {
                        int sz = strlen(S.index2name[i]);
                        if (lst + sz + 2 >= BUF_SIZE) { 
                            buf[lst++] = '\n'; lst = write(1, buf, lst); buf[0] = 'v'; lst = 1; 
                        }
                        buf[lst++] = ' ';
                        if (!S.best_model[i]) buf[lst++] = '-';
                        strcpy(buf+lst,S.index2name[i]); lst += sz;
                    }
        }
        buf[lst++] = '\n';
        if (lst + 20 >= BUF_SIZE) { lst = write(1, buf, lst); lst = 0; }
    }
    const char *out = NULL;
    if (optimum){
        if (S.best_goalvalue == Int_MAX) out = "s UNSATISFIABLE\n";
        else                             out = "s OPTIMUM FOUND\n";
    }else{
        if (S.best_goalvalue == Int_MAX) out = "s UNKNOWN\n";
        else if (opt_satisfiable_out)    out = "s SATISFIABLE\n";
        else                             out = "c SATISFIABLE\n";
    }
    if (out != NULL) strcpy(buf + lst, out), lst += strlen(out);
    lst = write(1, buf, lst); lst = 0;
    resultsPrinted = true;
}


void SIGINT_handler(int /*signum*/) {
    reportf("\n");
    reportf("*** INTERRUPTED ***\n");
    //SatELite::deleteTmpFiles();
    fflush(stdout);
    std::_Exit(0); }


void SIGTERM_handler(int signum) {
    if (opt_verbosity >= 1) {
        reportf("\n");
        reportf("*** TERMINATED by signal %d ***\n", signum);
        reportf("_______________________________________________________________________________\n\n");
        pb_solver->printStats();
        reportf("_______________________________________________________________________________\n");
    }
    handlerOutputResult(*pb_solver, false);
    //SatELite::deleteTmpFiles();
    //fflush(stdout);
    std::_Exit(0);
}

void increase_stack_size(int new_size) // M. Piotrow 16.10.2017
{
#if !defined(_MSC_VER) && !defined(__MINGW32__)
#include <sys/resource.h>
  
  struct rlimit rl;
  rlim_t new_mem_lim = new_size*1024*1024;
  getrlimit(RLIMIT_STACK,&rl);
  if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max) {
    rl.rlim_cur = new_mem_lim;
    if (setrlimit(RLIMIT_STACK, &rl) == -1)
      reportf("WARNING! Could not set resource limit: Stack memory.\n");
    else if (opt_verbosity > 1)
      reportf("Setting stack limit to %dMB.\n",new_size);
  }
#else
  (void) new_size;
  reportf("WARNING! Setting stack limit not supported on this architecture.\n");
#endif
}


PbSolver::solve_Command convert(Command cmd) {
    switch (cmd){
    case cmd_Minimize:      return PbSolver::sc_Minimize;
    case cmd_FirstSolution: return PbSolver::sc_FirstSolution;
    default: 
        assert(cmd == cmd_AllSolutions);
        return PbSolver::sc_AllSolutions;
    }
}

//=================================================================================================
