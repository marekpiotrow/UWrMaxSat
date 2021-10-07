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
#include "PbSolver.h"
#include "Hardware_reuse_sorters.h"

extern void oddEvenSelect(vec<Formula>& vars, unsigned k, int ineq);
extern void splitAndSortSubsequences(vec<Formula>& vars, vec<int>& positions, unsigned k, int ineq);
extern void oddEvenMultiMerge(vec<Formula>& vars, vec<int>& positions, unsigned k, int ineq);


struct seqGT { vec<int> &prevSeqSize; bool operator()(int i, int j) { return prevSeqSize[i] > prevSeqSize[j]; } }; 

static constexpr unsigned SubSeq = UINT_MAX - 7;

void ReuseSorters::encodeBySorter(vec<Formula>& fs, int k, int ineq)
{
  extern PbSolver *pb_solver;

  if (fs.size() == 0) return;

  pb_solver->totalSorterInputs += fs.size(); pb_solver->totalSorters++;

  if (fs.size() < minStoredSeqSize) { oddEvenSelect(fs, k, ineq); return; }

  // Note that in the values of type Formula given in fs, the 3 last bits are zeroes. 
  // We use them to store small counters in vectors: nfs, outfs and prev_elem.
  // If the counter is greater than 7, it is stored in the next element of a vector.

  vec<unsigned> nfs, outfs;
  vec<Pair<unsigned, unsigned> > usedfs;
  Map<unsigned, unsigned> unusedmap;
  unsigned cnt = 1, subseq_found = 0, fs_size = fs.size(), reused_size = 0;

  Sort::sort(fs);
  nfs.push(fs[0]);
  for (int i = 1; i < fs.size(); i++, cnt++)
      if (fs[i] != fs[i-1]) {
          if (cnt <= 7) nfs.last() |= cnt; else nfs.push(cnt);
          unusedmap.set(fs[i-1], cnt);
          cnt = 0;
          nfs.push(fs[i]);
      }
  if (cnt <= 7) nfs.last() |= cnt; else nfs.push(cnt);
  
  if (prev_seq.size() > 0 && fs.size() >= minAnalyzedSeqSize) {
      vec<int> cover;
      for (int i = 0; i < prev_seq.size(); i++) cover.push(prev_seq_size[i]);

      for (int i = 0; i < nfs.size(); nfs[i] & 7 ? i++ : i+=2) {
          unsigned cnt = nfs[i] & 7;
          if (cnt == 0 && nfs[i+1] > maxCount) {
              Pair<unsigned, unsigned> nf = Pair_new(nfs[i], nfs[i+1]);
              if (fnmap.has(nf)) {
                  vec<int>* used_in = fnmap.ref(nf);
                  for (int j = 0; j < used_in->size(); j++) cover[(*used_in)[j]] -= nfs[i+1];
              }
              cnt = maxCount;
          }
          while (cnt-- > 0) 
              if (fnnmap[cnt].has(nfs[i] & ~7)) {
                  vec<int>* used_in = fnnmap[cnt].ref(nfs[i] & ~7);
                  for (int j = 0; j < used_in->size(); j++) cover[(*used_in)[j]] -= cnt+1;
              }
      }
      cnt=0;
      for (int i = 0; i < cover.size(); i++)
          if (cover[i] == 0) cover[cnt++]=i;
      cover.shrink(cover.size() - cnt);
      seqGT cmp {prev_seq_size};
      if (cover.size() > 0) Sort::sort(cover, cmp);

      vec<int> rev_cover(prev_seq.size(), 0);
      for (int i = 0; i < cover.size(); i++) rev_cover[cover[i]] = i;

      for (int seq = 0; seq < cover.size(); seq++) {
          if (cover[seq] < 0) continue;
          // a subsequence found - insert it in outfs and update structures
          outfs.push(SubSeq); outfs.push(cover[seq]); reused_size += prev_seq_size[cover[seq]];
          vec<Pair<unsigned,unsigned> > usedtmp;
          updateCoverIndices(cover[seq], cover, rev_cover, usedtmp, unusedmap, true);
          for (int i = 0; i < usedtmp.size(); i++) usedfs.push(usedtmp[i]);
      }
      Sort::sort(usedfs);
      cnt = 0;
      for (int i = 1; i < usedfs.size(); i++)
          if (usedfs[i].fst == usedfs[i-1].fst) usedfs[cnt].snd += usedfs[i].snd;
          else usedfs[++cnt] = usedfs[i];
      usedfs.shrink(usedfs.size() - cnt - 1);
      subseq_found = outfs.size() / 2;
      for (int j = 0, i = 0; i < nfs.size(); nfs[i] & 7 ? i++ : i+=2)
          if (j < usedfs.size() && (nfs[i] & ~7) == usedfs[j].fst) {
              int cnt = nfs[i] & 7; if (cnt == 0) cnt = nfs[i+1];
              cnt -= usedfs[j].snd;
              if (cnt > 7) { outfs.push(usedfs[j].fst); outfs.push(cnt); }
              else if (cnt > 0) outfs.push(usedfs[j].fst | cnt);
              j++;
          } else { outfs.push(nfs[i]); if ((nfs[i] & 7) == 0) outfs.push(nfs[i+1]); }
  } else nfs.moveTo(outfs);
  if (subseq_found == 0) oddEvenSelect(fs, k, ineq);
  else {
      fs.clear();
      encodeWithReuse(outfs, 0, outfs.size(), fs, k, ineq);
  }
  if (outfs.size() != 2 || outfs[0] != SubSeq) {
      for (int i = 0; i < outfs.size(); i++) prev_elem.push(outfs[i]);
      vec<unsigned>& new_nfs = (nfs.size() == 0 ? outfs : nfs);
      for (int i = 0; i < new_nfs.size(); new_nfs[i] & 7 ? i++ : i+=2) {
          unsigned cnt = new_nfs[i] & 7;
          if (cnt != 0 || new_nfs[i+1] <= maxCount) {
              if (cnt == 0) cnt = new_nfs[i+1] - 1; else cnt--;
              if (!fnnmap[cnt].has(new_nfs[i] & ~7)) fnnmap[cnt].set(new_nfs[i] & ~7, new vec<int>());
              fnnmap[cnt].ref(new_nfs[i] & ~7)->push(prev_seq.size());
          } else {
              Pair<unsigned, unsigned> nf = Pair_new(new_nfs[i], new_nfs[i+1]);
              if (!fnmap.has(nf)) fnmap.set(nf, new vec<int>());
              fnmap.ref(nf)->push(prev_seq.size());
          }
      }
      if (opt_verbosity > 1 && reused_size > 0) { 
          reportf("Sorter[%d] reused inputs: %d out of %d (%d%%) [ ", 
                  prev_seq.size(), reused_size, fs_size, reused_size*100/fs_size);
          for (int i = (prev_seq.size() == 0 ? 0 : prev_seq.last()); i < prev_elem.size(); (prev_elem[i]&7)?i++:i+=2)
              if (prev_elem[i] == SubSeq) reportf("%d ",prev_elem[i+1]); else break;
          reportf("]\n");
      }
      pb_solver->totalReusedInputs  += reused_size;
      pb_solver->totalReusedPercent += reused_size*100/fs_size;
      prev_seq.push(prev_elem.size());
      prev_seq_size.push(fs_size);
  }
  nfs.clear();
  outfs.clear();
}

void ReuseSorters::updateCoverIndices(unsigned nr, vec<int>& cover, vec<int>& rev_cover, vec<Pair<unsigned,unsigned> >& usedfs,
        Map<unsigned, unsigned>& unusedmap, bool root_level)
{
  for (int i = (nr ? prev_seq[nr-1] : 0); i < prev_seq[nr]; prev_elem[i] & 7 ? i++ : i+=2)
      if (prev_elem[i] == SubSeq) {
          updateCoverIndices(prev_elem[i+1], cover, rev_cover, usedfs, unusedmap, false);
          cover[rev_cover[prev_elem[i+1]]] = -1;
      } else {
          unsigned cnt = prev_elem[i] & 7; if (cnt == 0) cnt = prev_elem[i+1];
          usedfs.push(Pair_new(prev_elem[i] & ~7, cnt));
      }
  if (root_level) {
      Sort::sort(usedfs);
      unsigned cnt = 0;
      for (int i = 1; i < usedfs.size(); i++)
          if (usedfs[i].fst == usedfs[i-1].fst) usedfs[cnt].snd += usedfs[i].snd;
          else usedfs[++cnt] = usedfs[i];
      usedfs.shrink(usedfs.size() - cnt - 1);
      for (int i = 0; i < usedfs.size(); i++) {
          unsigned& old_cnt = unusedmap.ref(usedfs[i].fst);
          if (old_cnt > maxCount) { 
              Pair<unsigned, unsigned> nf = Pair_new(usedfs[i].fst, old_cnt);
              if (fnmap.has(nf)) {
                  vec<int>* used_in = fnmap.ref(nf);
                  for (int j = 0; j < used_in->size(); j++) cover[rev_cover[(*used_in)[j]]] = -1;
              }
          }
          cnt = old_cnt - usedfs[i].snd;
          for (unsigned c = min(old_cnt,maxCount);  c > cnt; c--)
              if (fnnmap[c-1].has(usedfs[i].fst)) {
                  vec<int>* used_in = fnnmap[c-1].ref(usedfs[i].fst);
                  for (int j = 0; j < used_in->size(); j++) cover[rev_cover[(*used_in)[j]]] = -1;
              }
          old_cnt = cnt;
      }
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

