#!/usr/bin/env python3
"""Probe for the node SliceOscDecay (BeyondWordsLinear.lean): tabulate
levelOsc j a m / #levelSet j a  =  sum_{y < 3^a} |mu(y) - 3^{m-a} mu(y mod 3^m)| / card,
for slices a within +-2 of j/2 and all 1 <= m <= a.  Exact over all 2^j starts.
Pure Python (no numpy on the box).  Control: m = a gives 0 identically (lam = mu)."""
import sys
from collections import Counter

def slices(j, want):
    out = {a: Counter() for a in want}
    for r in range(2**j):
        x, a = r, 0
        for _ in range(j):
            if x & 1:
                x = (3*x + 1) >> 1; a += 1
            else:
                x >>= 1
        if a in out:
            out[a][x] += 1
    return out

def osc_row(mass, aa):
    cnt = sum(mass.values()); N = 3**aa
    row = []
    for m in range(1, aa + 1):
        M = 3**m
        cls = Counter()
        for y, c in mass.items():
            cls[y % M] += c
        q = 3.0**(m - aa)
        # occupied points: |mu - q cls|; empty lifts of class d: (#empty in class) * q cls(d)
        tot = 0.0; occ = Counter()
        for y, c in mass.items():
            tot += abs(c - q * cls[y % M]); occ[y % M] += 1
        per = N // M
        for d, c in cls.items():
            tot += (per - occ[d]) * q * c
        row.append(tot / cnt)
    return row

for j in map(int, sys.argv[1:]):
    want = list(range(j//2 - 2, j//2 + 3))
    sl = slices(j, want)
    for aa in want:
        row = osc_row(sl[aa], aa)
        print(f"j={j:2d} a={aa:2d} n={sum(sl[aa].values()):8d} " +
              " ".join(f"{v:.3f}" for v in row), flush=True)
