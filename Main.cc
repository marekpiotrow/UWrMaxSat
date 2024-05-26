/*****************************************************************************************[Main.cc]

Minisat+ -- Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson

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

/**************************************************************************************************

Read a DIMACS file and apply the SAT-solver to it.

**************************************************************************************************/


#include <unistd.h>
#include <signal.h>
#include <atomic>
#include <chrono>
#include <thread>
#include "System.h"
#include "MsSolver.h"
#include "PbParser.h"
#include "FEnv.h"
#include "Main_utils.h"

#ifdef MAXPRE
#include "preprocessorinterface.hpp"
#endif

//=================================================================================================


int main(int argc, char** argv)
{
#ifdef USE_SCIP
    extern std::atomic<char> opt_finder;
    time(&wall_clock_time);
#else
    char opt_finder = OPT_NONE;
#endif
  try {
    setOptions(argc, argv);
    pb_solver = new MsSolver(true, opt_preprocess);
    signal(SIGINT , SIGINT_handler);
    signal(SIGTERM, SIGTERM_handler);

    // Set command from 'PBSATISFIABILITYONLY':
    char* value = getenv("PBSATISFIABILITYONLY");
    if (value != NULL && atoi(value) == 1)
        reportf("Setting switch '-first' from environment variable 'PBSATISFIABILITYONLY'.\n"),
        opt_command = cmd_FirstSolution;

    if (opt_cpu_lim != INT32_MAX) {
        reportf("Setting cpu limit to %ds.\n",opt_cpu_lim);
#ifdef SIGXCPU	
        signal(SIGXCPU, SIGTERM_handler);
#endif	
        limitTime(opt_cpu_lim);
    }
    if (opt_mem_lim != INT32_MAX) {
        reportf("Setting memory limit to %dMB.\n",opt_mem_lim);
        signal(SIGSEGV, SIGTERM_handler); 
        signal(ENOMEM, SIGTERM_handler); 
        signal(SIGABRT, SIGTERM_handler);
        limitMemory(opt_mem_lim);
    }
    increase_stack_size(256); // to at least 256MB - M. Piotrow 16.10.2017
    if (opt_maxsat || opt_input != NULL && strcmp(opt_input+strlen(opt_input)-4, "wcnf") == 0) {
        opt_maxsat = true; 
        if (opt_minimization < 0) opt_minimization = 1; // alt (unsat based) algorithm
        if (opt_verbosity >= 1) reportf("Parsing MaxSAT file...\n");
        parse_WCNF_file(opt_input, *pb_solver);
        if (opt_convert == ct_Undef) opt_convert = ct_Sorters;
        if (opt_maxsat_msu) {
            if (opt_seq_thres < 0) opt_seq_thres = 4;
            pb_solver->maxsat_solve(convert(opt_command));
        } else {
            for (int i = pb_solver->soft_cls.size() - 1; i >= 0; i--)
                if (pb_solver->soft_cls[i].snd->size() > 1)
                    pb_solver->sat_solver.addClause(*pb_solver->soft_cls[i].snd);
            if (opt_minimization < 0) opt_minimization = 2; // bin (sat/unsat based) algorithm
            if (opt_seq_thres < 0) opt_seq_thres = 96;
            opt_reuse_sorters = false;
            pb_solver->solve(convert(opt_command));
        }
    } else {
        if (opt_verbosity >= 1) reportf("Parsing PB file...\n");
        opt_bin_model_out = false;
        {
            bool opt = opt_maxsat_msu; opt_maxsat_msu = false;
            parse_PB_file(opt_input, *pb_solver, opt_old_format);
            opt_maxsat_msu = opt;
        }
        if (opt_convert == ct_Undef) {
            opt_convert = ct_Mixed;
            if (opt_convert_goal == ct_Undef) opt_convert_goal = ct_Sorters;
        }
        if (!opt_maxsat_msu) {
            if (opt_minimization < 0) opt_minimization = 2; // bin (sat/unsat based) algorithm
            if (opt_seq_thres < 0) opt_seq_thres = 96;
            pb_solver->solve(convert(opt_command));
        } else {
            if (pb_solver->goal != NULL) {
                for (int i = 0; i < pb_solver->goal->size; i++) {
                    Minisat::vec<Lit> *ps_copy = new Minisat::vec<Lit>;
                    ps_copy->push(~(*pb_solver->goal)[i]);
#ifdef BIG_WEIGHTS                    
                    pb_solver->soft_cls.push(Pair_new((*pb_solver->goal)(i), ps_copy));
#else
                    pb_solver->soft_cls.push(Pair_new(tolong((*pb_solver->goal)(i)), ps_copy));
#endif                    
                }
                delete pb_solver->goal; pb_solver->goal = NULL;
            }
            if (opt_seq_thres < 0) opt_seq_thres = 4;
            if (opt_minimization < 0) opt_minimization = 1; // alt (unsat based) algorithm
            pb_solver->maxsat_solve(convert(opt_command));
        }
    }

    if (pb_solver->goal == NULL && pb_solver->soft_cls.size() == 0 && pb_solver->best_goalvalue == Int_MAX)
        opt_command = cmd_FirstSolution;    // (otherwise output will be wrong)
    if (!pb_solver->okay())
        opt_command = cmd_Minimize;         // (HACK: Get "UNSATISFIABLE" as output)

    // <<== write result to file 'opt_result'

    if (opt_command == cmd_Minimize) {
        if (opt_finder != OPT_SCIP) outputResult(*pb_solver, !pb_solver->asynch_interrupt);
    } else if (opt_command == cmd_FirstSolution) {
        if (opt_finder != OPT_SCIP) outputResult(*pb_solver, false);
    }

  } catch (Minisat::OutOfMemoryException&){
        if (opt_verbosity >= 1 && opt_finder != OPT_SCIP) {
          pb_solver->printStats();
          reportf("Out of memory exception caught\n");
        }
        if (opt_finder != OPT_SCIP) outputResult(*pb_solver, false);
  }
#ifdef USE_SCIP
  if (opt_scip_parallel)
	  std::this_thread::sleep_for(std::chrono::milliseconds(10));
#endif
  std::_Exit(exit_code); // (faster than "return", which will invoke the destructor for 'PbSolver')
}
