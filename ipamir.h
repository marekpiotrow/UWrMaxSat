/* Part of the generic incremental MaxSAT API called 'ipamir',
 * which is based on the incremental SAT API 'ipasir'.
 * See 'LICENSE' for rights to use this software.
 */
#ifndef ipamir_h_INCLUDED
#define ipamir_h_INCLUDED

#include <stdint.h>

/*
 * In this header, the macro IPAMIR_API is defined as follows:
 * - if IPAMIR_SHARED_LIB is not defined, then IPAMIR_API is defined, but empty.
 * - if IPAMIR_SHARED_LIB is defined...
 *    - ...and if BUILDING_IPAMIR_SHARED_LIB is not defined, IPAMIR_API is
 *      defined to contain symbol visibility attributes for importing symbols
 *      of a DSO (including the __declspec rsp. __attribute__ keywords).
 *    - ...and if BUILDING_IPAMIR_SHARED_LIB is defined, IPAMIR_API is defined
 *      to contain symbol visibility attributes for exporting symbols from a
 *      DSO (including the __declspec rsp. __attribute__ keywords).
 */

#if defined(IPAMIR_SHARED_LIB)
    #if defined(_WIN32) || defined(__CYGWIN__)
        #if defined(BUILDING_IPAMIR_SHARED_LIB)
            #if defined(__GNUC__)
                #define IPAMIR_API __attribute__((dllexport))
            #elif defined(_MSC_VER)
                #define IPAMIR_API __declspec(dllexport)
            #endif
        #else
            #if defined(__GNUC__)
                #define IPAMIR_API __attribute__((dllimport))
            #elif defined(_MSC_VER)
                #define IPAMIR_API __declspec(dllimport)
            #endif
        #endif
    #elif defined(__GNUC__)
        #define IPAMIR_API __attribute__((visibility("default")))
    #endif

    #if !defined(IPAMIR_API)
        #if !defined(IPAMIR_SUPPRESS_WARNINGS)
            #warning "Unknown compiler. Not adding visibility information to IPAMIR symbols."
            #warning "Define IPAMIR_SUPPRESS_WARNINGS to suppress this warning."
        #endif
        #define IPAMIR_API
    #endif
#else
    #define IPAMIR_API
#endif

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Return the name and the version of the incremental MaxSAT solving library.
 */
IPAMIR_API const char * ipamir_signature ();

/**
 * Construct a new solver and return a pointer to it. Use the returned pointer
 * as the first parameter in each of the following functions.
 *
 * Required state: N/A
 * State after: INPUT
 */
IPAMIR_API void * ipamir_init ();

/**
 * Release the solver, i.e., all its resources and allocated memory. The solver
 * pointer cannot be used for any purposes after this call.
 *
 * Required state: INPUT or OPTIMAL or SAT or UNSAT or ERROR
 * State after: undefined
 */
IPAMIR_API void ipamir_release (void * solver);

/**
 * Add the given literal into the currently added hard clause or finalize the
 * hard clause with a 0.
 * 
 * Clauses added by this function cannot be removed. The addition of removable
 * clauses can be simulated using activation literals and assumptions.
 *
 * Required state: INPUT or OPTIMAL or SAT or UNSAT
 * State after: INPUT
 *
 * Literals are encoded as (non-zero) integers as in the DIMACS formats. They
 * have to be smaller or equal to INT32_MAX and strictly larger than INT32_MIN
 * (to avoid negation overflow). This applies to all the literal arguments in
 * API functions.
 */
IPAMIR_API void ipamir_add_hard (void * solver, int32_t lit_or_zero);

/**
 * Declare the literal 'lit' soft and set its weight to 'weight'. After calling
 * this function, assigning lit to true incurs cost 'weight'. On a clausal
 * level, this corresponds to adding a unit soft clause containing the negation
 * of 'lit' and setting its weight to 'weight'.
 * 
 * Non-unit soft clauses C of weight w should be normalized by introducing a
 * new literal b, adding (C or b) as a hard clause via 'ipamir_add_hard', and
 * declaring b as a soft literal of weight w.
 * 
 * If 'lit' has already been declared as a soft literal, this function changes the
 * weight of 'lit' to 'weight'.
 *
 * Required state: INPUT or OPTIMAL or SAT or UNSAT
 * State after: INPUT
 */
IPAMIR_API void ipamir_add_soft_lit (void * solver, int32_t lit, uint64_t weight);

/**
 * Add an assumption for the next call of 'ipamir_solve'. After calling
 * 'ipamir_solve' all previously added assumptions are cleared.
 * 
 * Note that on a clausal level, assuming the negation of a soft literal 'lit'
 * (declared via 'ipamir_add_soft_lit') corresponds to hardening a soft clause.
 * 
 * Required state: INPUT or OPTIMAL or SAT or UNSAT
 * State after: INPUT
 */
IPAMIR_API void ipamir_assume (void * solver, int32_t lit);

/**
 * Solve the MaxSAT instance, as defined by previous calls to 'ipamir_add_hard'
 * and 'ipamir_add_soft_lit', under the assumptions specified by previous calls
 * to 'ipamir_assume' since the last call to 'ipamir_solve'.
 * 
 * A feasible solution is an assignment that satisfies the hard clauses and
 * assumptions. An optimal solution is a solution which minimizes the sum of
 * weights of soft literals set to true.
 * 
 * Return one of the following:
 * 
 * 0 -- If the search is interrupted and no feasible solution has yet been
 * found. The state of the solver is set to INPUT. Note that the solver can only
 * be interrupted via 'ipamir_set_terminate'.
 * 
 * 10 -- If the search is interrupted but a feasible solution has been found
 * before the interrupt occurs. The state of the solver is changed to SAT.
 * 
 * 20 -- If no feasible solution exists. The state of the solver is changed to
 * UNSAT.
 * 
 * 30 -- If an optimal solution is found. The state of the solver is changed to
 * OPTIMAL.
 * 
 * 40 -- If the solver is in state ERROR. The solver enters this state if a
 * sequence of ipamir calls have been made that the solver does not support.
 * 
 * This function can be called in any defined state of the solver. Note that
 * the state of the solver _during_ execution of 'ipamir_solve' is undefined.
 *
 * Required state: INPUT or OPTIMAL or SAT or UNSAT
 * State after: INPUT or OPTIMAL or SAT or UNSAT or ERROR
 */
IPAMIR_API int ipamir_solve (void * solver);

/**
 * Retuns the objective value of the current solution, i.e. the sum of weights
 * of all soft literals set to true.
 * 
 * This function can only be used if 'ipamir_solve' has returned 20 or 30, and
 * no 'ipamir_add_hard', 'ipamir_add_soft_lit', or 'ipamir_assume' has been
 * called since then, i.e., the state of the solver is OPTIMAL or SAT.
 * 
 * Required state: OPTIMAL or SAT
 * State after: OPTIMAL or SAT (unchanged)
 */
IPAMIR_API uint64_t ipamir_val_obj (void * solver);

/**
 * Get the truth value of the given literal in the found solution. Return 'lit'
 * if True, '-lit' if False, and 0 if not important.
 * 
 * This function can only be used if 'ipamir_solve' has returned 20 or 30, and
 * no 'ipamir_add_hard', 'ipamir_add_soft_lit', or 'ipamir_assume' has been
 * called since then, i.e., the state of the solver is OPTIMAL or SAT.
 *
 * Required state: OPTIMAL or SAT
 * State after: OPTIMAL or SAT (unchanged)
 */
IPAMIR_API int32_t ipamir_val_lit (void * solver, int32_t lit);

/**
 * Set a callback function used to indicate a termination requirement to the
 * solver. The solver will periodically call this function and check its return
 * value during the search. The ipamir_set_terminate function can be called in
 * any state of the solver, the state remains unchanged after the call.
 * The callback function is of the form "int terminate(void * state)"
 *   - it returns a non-zero value if the solver should terminate.
 *   - the solver calls the callback function with the parameter "state"
 *     having the value passed in the ipamir_set_terminate function (2nd parameter).
 *
 * Required state: INPUT or OPTIMAL or SAT or UNSAT
 * State after: INPUT or OPTIMAL or SAT or UNSAT (unchanged)
 */
IPAMIR_API void ipamir_set_terminate (void * solver, void * state, int (*terminate)(void * state));

#ifdef __cplusplus
} // closing extern "C"
#endif

#endif
