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

#include "Hardware.h"
#include "Map.h"
#include "Sort.h"
#include "Hardware_reuse_sorters.h"

extern void oddEvenSelect(vec<Formula>& vars, unsigned k, int ineq);
extern void splitAndSortSubsequences(vec<Formula>& vars, vec<int>& positions, unsigned k, int ineq);
extern void oddEvenMultiMerge(vec<Formula>& vars, vec<int>& positions, unsigned k, int ineq);


struct seqGT { vec<int> &prevSeqSize; bool operator()(int i, int j) { return prevSeqSize[i] > prevSeqSize[j]; } }; 

static constexpr unsigned SubSeq = UINT_MAX - 7;

void ReuseSorters::encodeBySorter(vec<Formula>& fs, int k, int ineq)
{
  if (fs.size() == 0) return;
  vec<unsigned> nfs, outfs, usedfs;
  unsigned cnt = 1, subseq_found = 0, fs_size = fs.size(), reused_size = 0;
  sort(fs);
  nfs.push(fs[0]);
  for (int i = 1; i < fs.size(); i++, cnt++)
      if (fs[i] != fs[i-1]) {
          if (cnt <= 7) nfs.last() |= cnt; else nfs.push(cnt);
          cnt = 0;
          nfs.push(fs[i]);
      }
  if (cnt <= 7) nfs.last() |= cnt; else nfs.push(cnt);
  
  if (prev_seq.size() > 0) {
      vec<int> cover;
      for (int i = 0; i < prev_seq.size(); i++) cover.push(prev_seq_size[i]);

      for (int i = 0; i < nfs.size(); nfs[i] & 7 ? i++ : i+=2) {
          unsigned cnt = nfs[i] & 7;
          Pair<unsigned, unsigned> nf;
          if (cnt == 0) nf = Pair_new(nfs[i], nfs[i+1]);
          if (cnt != 0 && fnnmap[cnt-1].has(nfs[i])) {
              vec<int>* used_in = fnnmap[cnt-1].ref(nfs[i]);
              for (int j = 0; j < used_in->size(); j++) cover[(*used_in)[j]] -= cnt;
          } else if (cnt == 0 && fnmap.has(nf)) {
              vec<int>* used_in = fnmap.ref(nf);
              for (int j = 0; j < used_in->size(); j++) cover[(*used_in)[j]] -= nfs[i+1];
          }
      }
      for (int from = 0, i = 0; i < prev_seq.size(); from = prev_seq[i++])
          for (int j = from; j < prev_seq[i] && prev_elem[j] == SubSeq; j+=2)
              if (cover[prev_elem[j+1]] == 0) cover[i] -= prev_seq_size[prev_elem[j+1]];
      cnt=0;
      for (int i = 0; i < cover.size(); i++)
          if (cover[i] == 0) cover[cnt++]=i;
      cover.shrink(cover.size() - cnt);
      seqGT cmp {prev_seq_size};
      if (cover.size() > 0) sort(cover, cmp);

      vec<int> rev_cover(prev_seq.size(), 0);
      for (int i = 0; i < cover.size(); i++) rev_cover[cover[i]] = i;

      for (int seq = 0; seq < cover.size(); seq++) {
          if (cover[seq] < 0) continue;
          vec<unsigned> queue; 
          bool ok = true;
          queue.push(cover[seq]); cover[seq] = -1;
          for (int j = 0; j < queue.size() && ok; j++)
              for (int s = queue[j], si = (s ? prev_seq[s-1] : 0); si < prev_seq[s] && prev_elem[si] == SubSeq; si+=2)
                  if (cover[rev_cover[prev_elem[si+1]]] < 0) { ok = false; break; } 
                  else queue.push(prev_elem[si+1]);
          if (!ok) continue;
          outfs.push(SubSeq); outfs.push(queue[0]); reused_size += prev_seq_size[queue[0]];
          updateCoverIndices(queue[0], cover, rev_cover, usedfs);
      }
      sort(usedfs);
      subseq_found = outfs.size() / 2;
      for (int j = 0, i = 0; i < nfs.size(); nfs[i] & 7 ? i++ : i+=2)
          if (j < usedfs.size() && (nfs[i] & ~7) == usedfs[j]) j++;
          else { outfs.push(nfs[i]); if ((nfs[i] & 7) == 0) outfs.push(nfs[i+1]); }
      nfs.clear();
  } else nfs.moveTo(outfs);
  if (subseq_found == 0) oddEvenSelect(fs, k, ineq);
  else {
      fs.clear();
      encodeWithReuse(outfs, 0, outfs.size(), fs, k, ineq);
  }
  if (outfs.size() != 2 || outfs[0] != SubSeq) {
      for (int i = 0; i < outfs.size(); outfs[i] & 7 ? i++ : i+=2) {
          prev_elem.push(outfs[i]);
          unsigned cnt = outfs[i] & 7;
          Pair<unsigned, unsigned> nf;
          if (cnt == 0) { prev_elem.push(outfs[i+1]); nf = Pair_new(outfs[i], outfs[i+1]); }
          if (outfs[i] != SubSeq) {
              if (cnt-- != 0) {
                  if (!fnnmap[cnt].has(outfs[i])) fnnmap[cnt].set(outfs[i], new vec<int>());
                  fnnmap[cnt].ref(outfs[i])->push(prev_seq.size());
              } else {
                  if (!fnmap.has(nf)) fnmap.set(nf, new vec<int>());
                  fnmap.ref(nf)->push(prev_seq.size());
              }
          }
      }
//reportf("[%d,%d]: ",prev_seq.size(),fs_size); for (int i = (prev_seq.size() == 0 ? 0 : prev_seq.last()); i < prev_elem.size(); (prev_elem[i]&7)?i++:i+=2) if (prev_elem[i] == SubSeq) reportf("SS(%d) ",prev_elem[i+1]); else if (prev_elem[i] & 7) reportf("%d*%d ",(prev_elem[i]&7), (prev_elem[i]&~7)); else reportf("%d*%d ", prev_elem[i], prev_elem[i+1]); reportf("\n");       
      if (opt_verbosity > 1 && reused_size > 0) { 
          reportf("Sorter[%d] reused inputs: %d out of %d (%d%%) [ ", 
                  prev_seq.size(), reused_size, fs_size, reused_size*100/fs_size);
          //for (int i = (prev_seq.size() == 0 ? 0 : prev_seq.last()); i < prev_elem.size(); (prev_elem[i]&7)?i++:i+=2)
          //    if (prev_elem[i] == SubSeq) reportf("%d ",prev_elem[i+1]); else break;
          reportf("]\n");
      }
      prev_seq.push(prev_elem.size());
      prev_seq_size.push(fs_size);
  }
  outfs.clear();
}

void ReuseSorters::updateCoverIndices(unsigned nr, vec<int>& cover, vec<int>& rev_cover, vec<unsigned>& usedfs)
{
  for (int i = (nr ? prev_seq[nr-1] : 0); i < prev_seq[nr]; prev_elem[i] & 7 ? i++ : i+=2)
      if (prev_elem[i] == SubSeq) updateCoverIndices(prev_elem[i+1], cover, rev_cover, usedfs);
      else {
          unsigned cnt = prev_elem[i] & 7;
          Pair<unsigned, unsigned> nf;
          if (cnt == 0) nf = Pair_new(prev_elem[i], prev_elem[i+1]);
          if (cnt != 0 && fnnmap[cnt-1].has(prev_elem[i]) || cnt == 0 && fnmap.has(nf)) {
              vec<int>* used_in = (cnt != 0 ? fnnmap[cnt-1].ref(prev_elem[i]) : fnmap.ref(nf));
              for (int j = 0; j < used_in->size(); j++) cover[rev_cover[(*used_in)[j]]] = -1;
          }
          usedfs.push(prev_elem[i] & ~7);
      }
}

void ReuseSorters::encodeWithReuse(vec<unsigned>&outfs, int from, int to, vec<Formula>& outvars, int k, int ineq)
{
    int subseq = from;
    vec<Formula> vars[2], tmp;
    vec<int> pos[2], positions;

    while (subseq < to && outfs[subseq] == SubSeq) subseq += 2;
    for (int i = subseq; i < to; outfs[i] & 7 ? i++ : i+=2) {
        unsigned cnt = outfs[i] & 7; if (cnt == 0) cnt = outfs[i+1];
        for (int j = cnt; j > 0; j--) vars[0].push(outfs[i] & ~7);
    }
    if (vars[0].size() > 0) splitAndSortSubsequences(vars[0], pos[0], k, ineq);
    pos[1].push(0);
    for (int i = from; i < subseq; i += 2) {
        int seq = outfs[i+1], sfrom = (seq ? prev_seq[seq-1] : 0), sto = prev_seq[seq];
        encodeWithReuse(prev_elem, sfrom, sto, tmp, k, ineq);
        for (int j = 0; j < tmp.size(); j++) vars[1].push(tmp[j]);
        pos[1].push(vars[1].size());
        tmp.clear();
    }
    positions.push(0);
    for (int i = 1, j = 1; i < pos[0].size() || j < pos[1].size(); ) {
        int beg, end, which;
        if (i < pos[0].size() && (j >= pos[1].size() || pos[0][i] - pos[0][i-1] > pos[1][j] - pos[1][j-1]))
             which = 0, beg = pos[0][i-1], end = pos[0][i], i++;
        else which = 1, beg = pos[1][j-1], end = pos[1][j], j++;
        for (int k = beg; k < end; k++) outvars.push(vars[which][k]);
        positions.push(outvars.size());
    }
    oddEvenMultiMerge(outvars, positions, k, ineq);
}

