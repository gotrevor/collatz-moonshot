#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Check: the slice family mu_{n,s} (law of X_n = sum_k 3^{k-1} 2^{-T_k} mod 3^n given T_n = s, gaps
a uniform composition) satisfies Tao's recursion slice-by-slice:
  mu_{n,s} = sum_g w(g) (x -> 2^{-g}(1+3x))_* mu_{n-1,s-g},  w(g) = C(s-g-1,n-2)/C(s-1,n-1).
Exact rational comparison for small (n, s)."""
from fractions import Fraction as F
from itertools import combinations
from math import comb
from collections import Counter
def direct(n, s):
    M = 3**n; out = Counter(); tot = 0
    for cut in combinations(range(1, s), n-1):          # T_1 < ... < T_{n-1} < T_n = s
        T = list(cut) + [s]
        x = sum(pow(3, k, M) * pow(pow(2, T[k], M), -1, M) for k in range(n)) % M
        out[x] += 1; tot += 1
    return {k: F(v, tot) for k, v in out.items()}
def recur(n, s):
    M = 3**n
    if n == 1: return {pow(pow(2, s, M), -1, M): F(1)}
    out = Counter()
    for g in range(1, s - (n-1) + 1):
        w = F(comb(s-g-1, n-2), comb(s-1, n-1))
        for y, p in direct(n-1, s-g).items():
            x = (pow(pow(2, g, M), -1, M) * (1 + 3*y)) % M
            out[x] += w * p
    return dict(out)
bad = 0
for n in range(1, 6):
    for s in range(n, n + 7):
        d, r = direct(n, s), recur(n, s)
        if d != {k: v for k, v in r.items() if v}: bad += 1; print("MISMATCH", n, s)
print("slices checked: n<=5, s in [n, n+6];", "all equal" if not bad else f"{bad} mismatches")
