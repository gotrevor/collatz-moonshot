#!/usr/bin/env python3
"""Rung-3 census instrument for the odd-block ladder (FRONT-A-PARADOXICAL follow-up).

Backs `FrontA/ThreeBlock.lean`.  A three-odd-block front-normalized word is
`[T]^b[F]^c[T]^d[F]^e[T]^f[F]^g` (b,c,d,e,f >= 1, g >= 0); m = b+c+d+e+f+g, k = b+d+f,
D = 2^m - 3^k.  Lean-proved facts this script exercises (all exact integers, no floats):

  threeBlock_criterion   n < tstep^[m] n   <=>   D*w1 <= 3^f*T - 2^(c+d+e+f),
                         T = 2^(c+d+e) - 2^(c+d) + 3^d*(2^c-1),  n+1 = 2^b*w1.
  threeBlock_cascade     3^b w1 + 2^c = 2^(c+d) w2 + 1,  3^d w2 + 2^e = 2^(e+f) w3 + 1,
                         3^f w3 = 2^g y + 1,  with w1,w2,w3 in N and w3 >= 1.

Minimising w1 over the cascade (w3 = 1, then w2 = ceil((2^(e+f)-2^e+1)/3^d), then
w1 = ceil((2^(c+d) w2 - 2^c + 1)/3^b)) gives the CEILING BOUND.  Results:

  * ceiling bound  -> 27 tuples in total, at lengths m in {5, 8, 16, 27}, exhaustive for all
    m <= 130 and every k with 3^k/2^m > 1/8.  Only the m = 8 block contains realized words
    (the four solutions); the 10 tuples at m in {5,16,27} are killed by the true realizing
    residue, by factors 10^2-10^3 (mode `verify`).
  * real relaxation only (drop the integrality of the interior scale w2; equivalently keep
    D*(2^(c+d+e+f) - T) <= 3^(b+d)*2^(c+d+e)*(3^f - 2^f), which is what w3 >= 1 alone gives)
    -> INFINITE: 18 tuples at m=8, 258 at m=16, 2489 at m=27, 18324 at m=46, still growing.

So rung 3's finiteness is carried by the two-level integer ceiling, not by a linear form in
logarithms -- unlike rung 2, whose crux `b + d <= 5` provably needs Baker (`sep_two_three`).

Usage:  python3 experiments/rung3_census.py census 130
        python3 experiments/rung3_census.py relax 46
        python3 experiments/rung3_census.py verify
"""
import sys, os
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paradoxical import numer_fast, realizing_residue_fast


def ceildiv(x, y):
    return -(-x // y)

def word(b, c, d, e, f, g):
    return [True]*b + [False]*c + [True]*d + [False]*e + [True]*f + [False]*g

def rhs(b, c, d, e, f, g):
    """3^f*T - 2^(c+d+e+f), the right-hand side of threeBlock_criterion."""
    T = 2**(c+d+e) - 2**(c+d) + 3**d * (2**c - 1)
    return 3**f * T - 2**(c+d+e+f)

def w1_ceiling(b, c, d, e, f, g):
    """Minimum of w1 over integer cascade triples with w3 >= 1."""
    w2 = ceildiv(2**(e+f) - 2**e + 1, 3**d)
    return ceildiv(2**(c+d) * w2 - 2**c + 1, 3**b)


def scan(mmax, ceiling=True):
    """Tuples passing the criterion at the minimal w1.  For each m only the k with
    3^k/2^m > 1/8 matter (that bracket is verified to contain every passer)."""
    out = {}
    for m in range(3, mmax + 1):
        M = 1 << m
        for k in range(1, m + 1):
            P = 3**k
            if P >= M or 8 * P <= M:
                continue
            D = M - P
            hits = []
            for b in range(1, k - 1):
                for d in range(1, k - b):
                    f = k - b - d
                    if f < 1:
                        continue
                    for c in range(1, m - k):
                        for e in range(1, m - k - c + 1):
                            g = m - k - c - e
                            if g < 0:
                                continue
                            if ceiling:
                                ok = D * w1_ceiling(b, c, d, e, f, g) <= rhs(b, c, d, e, f, g)
                            else:
                                T = 2**(c+d+e) - 2**(c+d) + 3**d * (2**c - 1)
                                ok = (D * (2**(c+d+e+f) - T)
                                      <= 3**(b+d) * 2**(c+d+e) * (3**f - 2**f))
                            if ok:
                                hits.append((b, c, d, e, f, g))
            if hits:
                out[(m, k)] = hits
    return out


def verify():
    """The realizing start of every ceiling-passer at m != 8: none is acyclic paradoxical."""
    for (m, k), tuples in sorted(scan(30).items()):
        for t in tuples:
            v = word(*t)
            M = 1 << len(v)
            D = M - 3**sum(v)
            num = numer_fast(v)
            n0 = realizing_residue_fast(v)
            while n0 <= 2:
                n0 += M
            print(f"m={m:3d} {t} n={n0:12d}  D*n={D*n0:18d}  numer={num:14d}"
                  f"  {'ACYCLIC PARADOXICAL' if D*n0 < num else 'no'}")


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "census"
    if mode == "verify":
        verify()
    else:
        mmax = int(sys.argv[2]) if len(sys.argv) > 2 else 40
        res = scan(mmax, ceiling=(mode == "census"))
        tot = sum(len(v) for v in res.values())
        print(f"{mode}: {tot} passing tuples, m <= {mmax}")
        for (m, k), v in sorted(res.items()):
            print(f"  m={m:3d} k={k:3d} R={float(Fraction(3**k, 1 << m)):.8f} n={len(v)}"
                  + (f"  {v}" if len(v) <= 6 else ""))
