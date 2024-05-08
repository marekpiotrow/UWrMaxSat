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
//#include <scip/scipdefplugins.h>
#include <vector>
//#include "MsSolver.h"

class MsSolver;

struct ScipSolver {
    SCIP *                   scip; 
    std::vector<SCIP_VAR *>  vars;
    std::vector<lbool>       model;
    int64_t                  obj_offset;
    bool                     must_be_started;

    ScipSolver() : scip(nullptr), obj_offset(0), must_be_started(false) {}
} ;

lbool scip_solve_async(SCIP *scip,
                       std::vector<SCIP_VAR *> vars,
                       std::vector<lbool> scip_model,
                       MsSolver *solver,
                       int64_t obj_offset);

#endif
