/***********************************************************************[Hardware_reuse_sorters.cc]
Copyright (c) 2021, Marek Piotrów

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

class ReuseSorters {
  private:
    vec<unsigned> prev_elem;
    vec<int> prev_seq, prev_seq_size;
    Map<Pair<unsigned, unsigned>, vec<int>* > fnmap;
    Map<unsigned, vec<int>* > fnnmap[7];

    void updateCoverIndices(unsigned nr, vec<int>& cover, vec<int>& rev_cover, vec<unsigned>& outfs);
    void encodeWithReuse(vec<unsigned>&outfs, int from, int to, vec<Formula>& outvars, int k, int ineq);
  public:
    void encodeBySorter(vec<Formula>& fs, int max_sel, int ineq);

} ;


