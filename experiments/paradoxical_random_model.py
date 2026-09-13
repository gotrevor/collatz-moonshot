#!/usr/bin/env python3
"""Random-residue baseline for the paradoxical census at a fixed near-critical (m, a).

For each front-normalized word v (first step odd, a odd steps, length m) the acyclic paradoxical
starts are exactly the n in v's residue class mod 2^m with D*n < numer(v).  If the realizing
residue were uniform on [0, 2^m), the chance the least start admits would be
    p(v) = min(1, numer(v) / (D * 2^m)),
so the expected number of admitting words is  E = sum_v p(v).  Compare with the exact census.

Usage: random_model.py M A [SAMPLES]   (exact enumeration if SAMPLES omitted; else Monte Carlo)"""
import sys, time, random
from math import comb
from itertools import combinations
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paradoxical import numer_fast

m, a = int(sys.argv[1]), int(sys.argv[2])
samples = int(sys.argv[3]) if len(sys.argv) > 3 else None
M = 2 ** m; D = M - 3 ** a
assert D > 0
total_words = comb(m - 1, a - 1)
t0 = time.time()

def p_of(odd_pos):
    v = [False] * m; v[0] = True
    for i in odd_pos:
        v[i] = True
    return min(1.0, numer_fast(v) / (D * M))

if samples is None:
    s = 0.0; n = 0
    for odd_pos in combinations(range(1, m), a - 1):
        s += p_of(odd_pos); n += 1
    print(f"m={m} a={a} D/2^m={D/M:.4f} words={n} E[admitting | uniform residue]={s:.3f} "
          f"(exact sum) [{time.time()-t0:.0f}s]", flush=True)
else:
    random.seed(1)
    s = 0.0
    for _ in range(samples):
        s += p_of(sorted(random.sample(range(1, m), a - 1)))
    mean = s / samples
    print(f"m={m} a={a} D/2^m={D/M:.4f} words={total_words} E[admitting | uniform residue]≈"
          f"{mean * total_words:.3f} (MC {samples} samples, mean p={mean:.3e}) [{time.time()-t0:.0f}s]",
          flush=True)
