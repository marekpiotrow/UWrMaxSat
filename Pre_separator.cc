/*******************************************************************************[Pre_separator.cc]
Copyright (c) 2021, Michał Karpiński and Marek Piotrów

The algorithm implemented below is based on the paper "On Preprocessing for Weigted MaxSAT", by
Tobias Paxian, Pascal Raiola and Bernd Becker

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

void separationIndex(const vec<weight_t>& cs, vec<int>& separation_points);
  // Find separation points (generalized Boolean multilevel optimization points) and put them
  // into the output vector (separation_points), where  cs is a sorted array of weights.

static weight_t gcd(weight_t n, weight_t m)
{
    if (n < 0) n = -n;
    if (m < 0) m = -m;
    while (m > 0) { weight_t x = m; m = n % m; n = x; }
    return n;
}

template <typename weight_sum_t>
static char isSeparating(const vec<weight_t>& cs, int idx, weight_sum_t bound) {
  int i, in_size = cs.size(), max_operations = 100000000, max_vec_size = 10000000;
  vec<weight_sum_t> weight_sums, shifted_weight_sums; 
  weight_sums.push(0);

  for (i = idx; i < in_size && max_operations > 0; i++) {
    // copy the weight_sums
    if (i == idx || cs[i] != cs[i-1]) weight_sums.copyTo(shifted_weight_sums);

    // shift weights by cs[i]
    for(int j = shifted_weight_sums.size() - 1; j >= 0; j--)
      shifted_weight_sums[j] += cs[i];

    // merge both lists removing duplicates to get new weight_sums
    vec<weight_sum_t> new_weight_sums;
    int k, l, n, m;
    n = weight_sums.size();
    m = shifted_weight_sums.size();
    if (n + m > max_vec_size) return 'M'; // vectors are too big

    new_weight_sums.push(0);
    weight_sum_t last = 0;
    for (k = 1, l = 0; k < n && l < m; ) {
      if (weight_sums[k] <= shifted_weight_sums[l]) {
        if (weight_sums[k] == shifted_weight_sums[l]) l++; // remove a duplicate
        new_weight_sums.push(std::move(weight_sums[k++]));
      } else
        new_weight_sums.push(shifted_weight_sums[l++]);
      if (new_weight_sums.last() - last < bound) return 'N'; // check separation condition
      else last = new_weight_sums.last(); 
    }
    if ((k < n && weight_sums[k] - last < bound) || (l < m && shifted_weight_sums[l] - last < bound))
        return 'N';
    while (k < n) new_weight_sums.push(std::move(weight_sums[k++]));
    new_weight_sums.moveTo(weight_sums);
    while (l < m) weight_sums.push(shifted_weight_sums[l++]);

    // subtract estimated number of operations performed in a loop
    max_operations -= n;
  }

  if (i == in_size)
    return 'S'; // is separating
  else
    return 'T'; // timeout reached
}

void separationIndex(const vec<weight_t>& cs, vec<int>& separation_points) {

  if (cs.size() <= 2) return;

  vec<Int> lw;
  separation_points.clear();

  // calculate prefix sums of weights
  lw.push(cs[0]);
  for(int i=1; i<cs.size(); i++) { lw.push(Int(cs[i]) + lw[i-1]); }

  weight_t rdiff = WEIGHT_MAX, rgcd = cs[cs.size()-1];

  // search for separation points (generalized Boolean multilevel optimization points)
  for (int i = cs.size() - 2; i > 1; i--) {
      rgcd = gcd(cs[i], rgcd);
      rdiff = min(rdiff, cs[i] == cs[i+1] ? WEIGHT_MAX : cs[i+1] - cs[i]);
      bool final_split = lw[i-1] <= rgcd;
      bool potential_split = lw[i-1] <= cs[i] && lw[i-1] <= rdiff;
      char res = 'N';
#ifdef BIG_WEIGHTS
      if (final_split || potential_split && (res = isSeparating<Int>(cs, i, lw[i-1])) == 'S')
          separation_points.push(i);
#else
      if (final_split || potential_split && (res =
          (lw.last() > Int(std::numeric_limits<uint64_t>::max()) ? isSeparating<Int>(cs, i, lw[i-1]) :
                                                isSeparating<uint64_t>(cs, i, toulong(lw[i-1])))) == 'S')
          separation_points.push(i);
#endif
      if (res == 'T' || res == 'M') break;
  }
}
