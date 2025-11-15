/**************************************************************************************[MsSolver.cc]
  Copyright (c) 2024, Marek Piotrów

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

#ifdef USE_SCIP

#include <scip/scip.h>
#include <vector>
#include <future>

class MsSolver;

struct ScipSolver {
    SCIP *                   scip; 
    std::vector<SCIP_VAR *>  vars;
    std::vector<lbool>       model;
    int64_t                  obj_offset;
    bool                     pb_decision_problem;
    bool                     must_be_started;
    bool                     started;
    bool                     interrupted;
    std::future<lbool>       asynch_result;
    vec<Lit>                 fixed_vars;

    ScipSolver() : scip(nullptr), obj_offset(0), pb_decision_problem(false), must_be_started(false),
                   started(false), interrupted(false) {}
} ;

void  scip_interrupt_solve(ScipSolver &scip);

lbool scip_solve_async(ScipSolver *scip_solver, MsSolver *solver);

#endif
