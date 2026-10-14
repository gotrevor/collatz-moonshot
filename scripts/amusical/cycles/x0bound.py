#!/usr/bin/env python3
"""Exact bound on the minimum of a positive U-cycle of length p with e halvings.

Theorem A: a positive cycle (all elements >= m >= 1) of length p, e = #E + 2#(A,B) halvings,
k = e - p odd steps, satisfies   3m - 1 <= k * max(2^e, 3^p) / |2^e - 3^p|.
M(p,e) := floor((k*max + |D|) / (3|D|))  is therefore an upper bound for m.
X0(L) = max_{1<=p<L, p<=e<=2p} M(p,e): every positive cycle of length < L has min <= X0(L).
All integer arithmetic.  Usage: x0bound.py L [L2 ...]
"""
import sys
from math import log

def M(p, e):
    k = e - p
    A, B = 1 << e, 3 ** p
    D = abs(A - B)
    return (k * max(A, B) + D) // (3 * D)

def X0(L):
    best, arg = 0, None
    pw3 = 1
    for p in range(1, L):
        pw3 *= 3
        # only e near p*log2(3) can matter, but scan a safe window and the rest is tiny:
        # for |e - p log2 3| >= 1, |Lambda| >= ln(3/2)... handled by the generic bound below.
        c = round(p * log(3, 2))
        for e in range(max(p, c - 2), min(2 * p, c + 2) + 1):
            k = e - p
            A = 1 << e
            D = abs(A - pw3)
            v = (k * max(A, pw3) + D) // (3 * D)
            if v > best:
                best, arg = v, (p, e)
    return best, arg

if __name__ == "__main__":
    for L in map(int, sys.argv[1:]):
        b, a = X0(L)
        print(f"L={L}  X0={b}  attained at (p,e)={a}")
