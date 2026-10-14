#!/usr/bin/env python3
"""Log-free Theorem A* :  a positive U-cycle (length p, e halvings, k = e - p odd steps, min m) has
      3^p (3m-1)^k  <=  2^e (3m)^k  <=  3^p (3m+1)^k.
X0*(L) = largest m >= 1 satisfying this for some 1 <= p < L, p <= e <= 2p (exact integers).
Also prints the A'' variant  m <= 1 + k/(4|Λ|)  (|Λ| >= |2^e-3^p|/max) for comparison.
Usage: x0exact.py L ...
"""
import sys
def ok(p, e, m):
    k = e - p
    a, b = 3 ** p, 1 << e
    return a * (3 * m - 1) ** k <= b * (3 * m) ** k <= a * (3 * m + 1) ** k
def maxm(p, e):
    # condition is monotone in m (the window shrinks as m grows): binary search for the largest m
    if not ok(p, e, 1): return 0
    lo, hi = 1, 2
    while ok(p, e, hi): lo, hi = hi, hi * 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if ok(p, e, mid): lo = mid
        else: hi = mid
    return lo
for L in map(int, sys.argv[1:]):
    best = (0, None); bestA2 = (0, None)
    for p in range(1, L):
        for e in range(p, 2 * p + 1):
            if e - p == 0: continue            # k = 0: 2^p = 3^p impossible
            mm = maxm(p, e)
            if mm > best[0]: best = (mm, (p, e))
            A, B = 1 << e, 3 ** p; D = abs(A - B)
            a2 = 1 + (e - p) * max(A, B) // (4 * D)
            if a2 > bestA2[0]: bestA2 = (a2, (p, e))
    print(f"L={L}: X0*={best[0]} at (p,e)={best[1]};  A'' bound={bestA2[0]} at {bestA2[1]}")
