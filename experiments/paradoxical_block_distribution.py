#!/usr/bin/env python3
"""Block-count distribution of admitting acyclic paradoxical words at a fixed (m, a):
all front-normalized words (first step odd) of length m with a odd steps, tallied by number of
odd blocks.  Usage: block_dist.py M A"""
import sys, time
from itertools import combinations
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from paradoxical import numer_fast, realizing_residue_fast

def admits_acyclic(v):
    m = len(v); a = sum(v); p = 3 ** a; M = 2 ** m
    if p >= M:
        return None
    d = M - p; num = numer_fast(v); r = realizing_residue_fast(v)
    n0 = r
    while n0 <= 2:
        n0 += M
    return n0 if d * n0 < num else None

m, a = int(sys.argv[1]), int(sys.argv[2])
t0 = time.time(); n = 0
by_blocks = {}; examples = {}
for odd_pos in combinations(range(1, m), a - 1):      # position 0 is odd (front-normalized)
    v = [False] * m; v[0] = True
    for i in odd_pos:
        v[i] = True
    n += 1
    n0 = admits_acyclic(v)
    if n0 is not None:
        b = sum(1 for i in range(m) if v[i] and (i == 0 or not v[i - 1]))
        by_blocks[b] = by_blocks.get(b, 0) + 1
        examples.setdefault(b, (''.join('T' if x else 'F' for x in v), n0))
print(f"m={m} a={a} D/2^m={(2**m-3**a)/2**m:.4f} words={n} admitting={sum(by_blocks.values())} "
      f"by_blocks={dict(sorted(by_blocks.items()))} [{time.time()-t0:.0f}s]", flush=True)
for b in sorted(examples):
    print(f"  blocks={b} e.g. {examples[b]}")
