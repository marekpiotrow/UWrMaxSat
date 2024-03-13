/*************************************************************************[PbSolver_convertSort.cc]
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
#include "Debug.h"
#include "HashQueue.h"

//#define pf(format, args...) (reportf(format, ## args), fflush(stdout))
#define pf(format, args...) nothing()

void nothing(void) {}


//=================================================================================================


//#define PickSmallest
#define ExpensiveBigConstants
#define AllDigitsImportant

int primes[] = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47 };
//int primes[] = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97 };
//int primes[] = { 2, 3, 4, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997 };

static inline int finalCost(vec<Int>& seq, int cost)
{
    // "Base case" -- don't split further, build sorting network for current sequence:
    int final_cost = cost;
    for (int i = 0; i < seq.size(); i++){
        if (seq[i] > INT_MAX)
            return INT_MAX;
      #ifdef ExpensiveBigConstants
        final_cost += toint(seq[i]);
      #else
        int c; for (c = 1; c*c < seq[i]; c++);
        final_cost += c;
      #endif
        if (final_cost < 0)
            return INT_MAX;
    }
    return final_cost;
}

/*static
int totalCost(vec<Int>& seq, vec<int>& base)
{
    vec<Int> s; seq.copyTo(s);
    int cost = 0, carry = 0;

    for (int i = 0; i < base.size(); i++){
        int p    = base[i];
        int last = 0, rest = carry;   // Sum of all the remainders.
        Int div;

        for (int j = 0; j < s.size(); j++){
            rest += toint(s[j] % Int(p));
            div = s[j] / Int(p);
            if (div > 0) s[last++] = div;
        }
        s.shrink(s.size()-last); cost += rest; carry = rest/p;
    }
    return finalCost(s, cost);
}*/

static
void optimizeBase(vec<Int>& seq, int carry_ins,int cost, vec<int>& base, int& cost_bestfound, vec<int>& base_bestfound,
    HashQueue *Q)
{
    vec<Int> new_seq;

    for (int i = 0; i < (int)elemsof(primes) && primes[i] <= opt_base_max; i++){
        int p    = primes[i];
        int rest = carry_ins;   // Sum of all the remainders.
        Int div, rem;

        for (int j = 0; j < seq.size(); j++){
            rest += toint(seq[j] % Int(p));
            div = seq[j] / Int(p);
            if (div > 0)
                /**/pf(" %d", div),
                new_seq.push(div);
        }

        int new_cost = cost+rest - carry_ins*3/4, new_carry_ins = rest/p;
        if (new_cost < cost_bestfound && new_cost + new_seq.size() <= cost_bestfound) {
            base.push(p);
            int final_cost = finalCost(new_seq, new_cost);
            if (final_cost < cost_bestfound){
                base.copyTo(base_bestfound);
                cost_bestfound = final_cost;
            }
            if (Q == NULL || base.size() > HashQueue::maxBaseSize)
                optimizeBase(new_seq, new_carry_ins, new_cost, base, cost_bestfound, base_bestfound, Q);
            else Q->push(base, new_cost, new_carry_ins);
            base.pop();
        }
        if (Q == NULL) return;
        new_seq.clear();
    }
}

static
void optimizeBase(vec<Int>& seq, int& cost_bestfound, vec<int>& base_bestfound)
{
    HashQueue Q;
    vec<Int>    new_seq;
    vec<int>    base;
    cost_bestfound = finalCost(seq,0);
    base_bestfound.clear();
    optimizeBase(seq, 0, 0, base, cost_bestfound, base_bestfound, NULL);
    base.clear(); Q.push(base,0,0);
    while (!Q.isEmpty()) {
        int carry_ins, cost = Q.popMin(base,carry_ins);
        if (cost >= cost_bestfound) break;
        new_seq.clear();
        Int prod = 1;
        for (int i=base.size()-1; i >= 0; i--) prod *= base[i];
        for (int i=0; i < seq.size(); i++) {
            Int div = seq[i] / prod;
            if (div > 0) new_seq.push(div);
        }
        optimizeBase(new_seq, carry_ins, cost, base, cost_bestfound, base_bestfound, &Q);        
    }
    Q.clear();
}


//=================================================================================================

#define lit2fml(p) id(var(var(p)),sign(p))


static
int buildSorter(vec<Formula>& ps, vec<int>& Cs, vec<Formula>& out_sorter, int max_sel, int ineq, bool soft_constr, vec<Formula>& base_assump, int base_assump_from)
{
  int count0 = 0, count1 = 0;
    out_sorter.clear();
    for (int i = 0; i < ps.size(); i++)
        if (ps[i] == _0_) count0 += Cs[i];
        else if (ps[i] == _1_) count1 += Cs[i];
        else if (ps[i] == _undef_)
            for (int j = 0; j < Cs[i]; j++)
                out_sorter.push(base_assump[base_assump_from++]);
        else
            for (int j = 0; j < Cs[i]; j++)
                out_sorter.push(ps[i]);
    int reusedCost = encodeBySorter(out_sorter, max_sel, ineq, soft_constr); // (overwrites inputs)
    if (count1 > 0) {
        out_sorter.growTo(out_sorter.size()+count1);
	for (int i=out_sorter.size()-1; i >= count1; i--) out_sorter[i] = out_sorter[i-count1];
	for (int i=0; i < count1; i++) out_sorter[i] = _1_;
    }
    if (count0 > 0) out_sorter.growTo(out_sorter.size()+count0,_0_);
    return reusedCost;
}

static
int buildSorter(vec<Formula>& ps, vec<Int>& Cs, vec<Formula>& out_sorter, int max_sel, int ineq, bool soft_constr, vec<Formula>& base_assump, int base_assump_from)
{
    vec<int>    Cs_copy;
    for (int i = 0; i < Cs.size(); i++)
        Cs_copy.push(toint(Cs[i]));
    return buildSorter(ps, Cs_copy, out_sorter, max_sel, ineq, soft_constr, base_assump, base_assump_from);
}


class Exception_TooBig {};

static
void buildConstraint(vec<Formula>& ps, vec<Int>& Cs, vec<Formula>& carry, vec<int>& base, int digit_no, vec<Formula>& out_digits, 
        int& max_cost, int max_sel, int ineq, bool soft_constr, vec<Formula>& base_assump, int base_assump_from)
{
    assert(ps.size() == Cs.size());

    if (FEnv::topSize() > max_cost) throw Exception_TooBig();
    /**
    pf("buildConstraint(");
    for (int i = 0; i < ps.size(); i++)
        pf("%d*%s ", Cs[i], (*debug_names)[index(ps[i])]);
    pf("+ %d carry)\n", carry.size());
    **/

    if (digit_no == base.size()){
        // Final digit, build sorter for rest:
        vec<Formula> sorted;
        max_cost -= buildSorter(ps, Cs, sorted, max_sel, ineq, soft_constr, base_assump, -1);
        // Add carry bits:
        encodeByMerger(sorted, carry, out_digits,  max_sel, ineq);
        if (FEnv::topSize() > max_cost) throw Exception_TooBig();
    }else{
        vec<Formula>    ps_rem;
        vec<int>        Cs_rem;
        vec<Formula>    ps_div;
        vec<Int>        Cs_div;

        // Split sum according to base:
        int B = base[digit_no];
        for (int i = 0; i < Cs.size(); i++){
            Int div = Cs[i] / Int(B);
            int rem = toint(Cs[i] % Int(B));
            if (div > 0){
                ps_div.push(ps[i]);
                Cs_div.push(div);
            }
            if (rem > 0){
                ps_rem.push(ps[i]);
                Cs_rem.push(rem);
            }
        }

        // Build sorting network:
        vec<Formula> sorted, result;
        max_cost -= buildSorter(ps_rem, Cs_rem, sorted, -1, ineq, soft_constr, base_assump, base_assump_from);
        // Add carry bits:
        encodeByMerger(sorted, carry, result, sorted.size()+carry.size(), ineq);

        // Get carry bits:
        carry.clear();
        for (int i = B-1; i < result.size(); i += B)
            carry.push(result[i]);

        /*out_digits.push();
        for (int i = 0; i < B-1; i++){
            Formula out = _0_;
            for (int j = 0; j < result.size(); j += B){
                int n = j+B-1;
                if (j + i < result.size())
                    out |= result[j + i] & ((n >= result.size()) ? _1_ : ~result[n]);
            }
            out_digits.last().push(out);
        }*/

        buildConstraint(ps_div, Cs_div, carry, base, digit_no+1, out_digits, max_cost, max_sel, ineq, soft_constr, base_assump, base_assump_from+B-1); //change to normal loop
    }
}

static
void set_assumptions(vec<Lit>& assump, Int val, const vec<int>& base, const vec<Formula>& base_assump)
{
    //assump.clear();
    for (int ba_from = 0, i = 0; i < base.size(); val /= base[i], ba_from += base[i]-1, i++) {
        int rem = toint(val % base[i]);
        if (rem > 0) assump.push(mkLit(index(base_assump[ba_from + rem - 1]),false));
        if (rem < base[i] - 1) assump.push(mkLit(index(base_assump[ba_from + rem]),true));
    }
}

/*
Naming:
  - a 'base' is a vector of integers, stating how far you count at that position before you wrap to the next digit (generalize base).
  - A 'dig' is an integer representing a digit in a number of some base.
  - A 'digit' is a vector of formulas, where the number of 1:s represents a digit in a number of some base.
*/

static
Formula buildConstraint(vec<Formula>& ps, vec<Int>& Cs, vec<int>& base, Int lo, Int hi, bool soft_constr, int max_cost, 
        vec<Formula>& base_assump, bool lastEncodingOK)
{
  extern PbSolver *pb_solver;
  vec<Formula> carry;
  vec<Formula> last_digit;
  Formula ret = _1_;
  //bool shared_fmls = opt_shared_fmls;
  
  Int B = 1, csum = 0;
  for (int i=0; i < base.size(); i++) B *= Int(base[i]);
  for (int i=0; i < Cs.size(); i++) csum += Cs[i];
  if (lo != Int_MIN && lo > 0) {
    Int rem    = lo % B;
    int lo_val = toint(lo / B);
    static int old_lo_val = INT_MAX;
    if (base_assump.size() > 0) {
        if (rem != 0) lo_val++;
        if (lo_val > old_lo_val) old_lo_val = lo_val;
        ps.push(_undef_); Cs.push(B-1);
        set_assumptions(pb_solver->base_assump,(rem != 0 ? B-rem : 0), base, base_assump);
    } else if (rem != 0) old_lo_val = ++lo_val, ps.push(_1_), Cs.push(B-rem);
    else if (lastEncodingOK) old_lo_val = max(old_lo_val, lo_val);
    else old_lo_val = lo_val;
    //if (hi != INT_MAX) opt_shared_fmls = true;

    buildConstraint(ps, Cs, carry, base, 0, last_digit, max_cost, old_lo_val, 1, soft_constr, base_assump, 0);

    if (base_assump.size() > 0 || rem != 0) ps.pop(), Cs.pop();
    
    ret &= last_digit[lo_val-1];
  }
  if (hi != Int_MAX) {
    //for(int i=0; i<ps.size(); i++) ps[i] = neg(ps[i]);
    hi += 1; // = csum - hi;
    
    Int rem    = hi % B;
    int hi_val = toint(hi / B);
    static int old_hi_val = 0;
    if (!lastEncodingOK) old_hi_val = 0;
    if (base_assump.size() > 0) {
        if (rem != 0) hi_val++;
        if (hi_val > old_hi_val) old_hi_val = hi_val; 
        ps.push(_undef_); Cs.push(B-1);
        set_assumptions(pb_solver->base_assump,(rem != 0 ? B-rem : 0), base, base_assump);
    } else if (rem != 0) old_hi_val = ++hi_val, ps.push(_1_), Cs.push(B-rem);
    else if (lastEncodingOK) old_hi_val = max(old_hi_val, hi_val);
    else old_hi_val = hi_val;

    carry.clear(); last_digit.clear();
    buildConstraint(ps, Cs, carry, base, 0, last_digit, max_cost, old_hi_val, -2, soft_constr, base_assump, 0);

    if (base_assump.size() > 0 || rem != 0) ps.pop(), Cs.pop();
    //for(int i=0; i<ps.size(); i++) ps[i] = neg(ps[i]);
    
    ret &= ~last_digit[hi_val-1];
  }
  //opt_shared_fmls = shared_fmls;
  return ret;
}


// Will return '_undef_' if 'cost_limit' is exceeded.
//
Formula buildConstraint(const Linear& c, bool soft_constr, int max_cost)
{
    static vec<Formula>    last_ps;
    static vec<Int>        last_Cs;
    static Int last_lo = Int_MIN, last_hi = Int_MAX;
    static int last_cost = 0;
    static Formula last_ret = _undef_;
    static bool negate = true;
    int sizesDiff = last_Cs.size() - c.size;
    bool lastBaseOK = sizesDiff >= 0;    
    Int sum = 0;

    for (int i = 0; i < c.size; i++) sum += c(i);
        
    for (int i = 0, j = 0; lastBaseOK && j < c.size; j++) {
        while (i < last_Cs.size() && c(j) > last_Cs[i]) i++;
        if (i == last_Cs.size() || c(j) < last_Cs[i]) lastBaseOK = false; else i++;
    }
    bool lastEncodingOK = lastBaseOK && opt_shared_fmls && FEnv::stack.size() > 0;
    Int sumAssigned = 0, sumSetToTrue = 0;
    extern PbSolver *pb_solver;
    int j = 0;
    for (int i = 0; lastEncodingOK && i < last_ps.size(); i++) {
        Lit   psi_lit = mkLit(index(last_ps[i]),sign(last_ps[i]));
        lbool psi_val = pb_solver->value(psi_lit);
        if (j < c.size && psi_lit == (negate ? ~c[j] : c[j]) && last_Cs[i] == c(j)) j++;
        else if (psi_val != l_Undef) {
            if (psi_val == l_True) sumSetToTrue += last_Cs[i];
            sumAssigned += last_Cs[i];
        }
        else if (j < c.size) lastEncodingOK = false;
    }
    if (j < c.size) lastEncodingOK = false;
    //negate = (c.hi == Int_MAX && c(c.size-1) == 1 && c.lo >= sum/2 && !lastEncodingOK || negate && lastEncodingOK) 
    //             && opt_maxsat && opt_minimization == 1 && c.size > 1000;
    if (negate) {
        last_lo = c.hi == Int_MAX ? Int_MIN : sum - c.hi;
        last_hi = c.lo == Int_MIN ? Int_MAX : sum - c.lo;
    } else last_lo = c.lo, last_hi = c.hi;
    if (!lastEncodingOK) {
        last_ps.clear(), last_Cs.clear();
        for (int j = 0; j < c.size; j++)
	    last_ps.push(negate ? neg(lit2fml(c[j])) : lit2fml(c[j])),
            last_Cs.push(c(j));
    } else {
        sum += sumAssigned;
        if (last_lo != Int_MIN) last_lo += sumSetToTrue;
        if (last_hi != Int_MAX) last_hi += sumSetToTrue;
    }
    int      cost;
    static vec<int> base;
    static vec<Formula> base_assump;
    if (!lastBaseOK || !lastEncodingOK && sizesDiff > 0 && 
                                      (base.size() <= 8 || sizesDiff * 8 > c.size)) {
        optimizeBase(last_Cs, cost, base);
        base_assump.clear();
        /**/pf("cost=%d, base.size=%d\n", cost, base.size());
    } else if (sizesDiff == 0 && last_ret == _undef_ && last_cost > max_cost) return _undef_;
    else if (!pb_solver->use_base_assump) {
        Int B = 1;
        for (int i = 0; i < base.size(); i++)
            if ((B *= (Int)base[i]) > sum) { base.shrink(base.size() - i); break; }
    }
    FEnv::push();
    if (pb_solver->use_base_assump) {
        if (base.size() == 0 || last_lo != Int_MIN && last_hi != Int_MAX) { base_assump.clear(); /*pb_solver->use_base_assump = false;*/ }
        else if (base_assump.size() == 0) {
            for (int i = 0; i < base.size(); i++) {
                Lit prev_p = lit_Undef;
                for (int j = 1; j < base[i]; j++) {
#ifdef MINISAT
                    Lit p = mkLit(pb_solver->sat_solver.newVar(l_Undef, !opt_branch_pbvars));
#else
                    Lit p = mkLit(pb_solver->sat_solver.newVar(true /*l_Undef*/, !opt_branch_pbvars));
#endif
                    pb_solver->sat_solver.setFrozen(var(p), true);
                    base_assump.push(lit2fml(p));
                    if (j > 1) pb_solver->sat_solver.addClause(~p,prev_p);
                    prev_p = p;
                }
            }
        }
    }
    Formula ret;
    try {
        ret = buildConstraint(last_ps, last_Cs, base, last_lo, last_hi, soft_constr, max_cost, base_assump, lastBaseOK);
    }catch (Exception_TooBig){
        last_cost = FEnv::topSize();
        FEnv::pop();
        removeLastSequences();
        last_ret = _undef_;
        return _undef_;
    }

    if (opt_verbosity >= 2) {
        if (FEnv::topSize() > 0) {
            reportf("Sorter-cost:%5d     ", FEnv::topSize());
            reportf("Base:"); for (int i = 0; i < base.size(); i++) reportf(" %d", base[i]); reportf("\n");
        } else if (!opt_maxsat && !pb_solver->use_base_assump) reportf("\n");
    }
    last_cost = FEnv::topSize(), last_ret = ret;
    if (opt_maxsat_msu && opt_minimization == 1) FEnv::stack.pop();
    else FEnv::keep();
    keepLastSequences();

    return c.lit==lit_Undef || pb_solver->use_base_assump ? ret : ~lit2fml(c.lit) | ret ;
}
