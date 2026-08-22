#!/usr/bin/env -S uv run --quiet python3
"""Same question, deduplicated by NECKLACE (gcd and circuit count are both
rotation-invariant, so counting words inflates every sample by a factor of k).

Route 2 premise: integer cycles should want FEW circuits.  Test: do necklaces
with the largest gcd(W,D) - the near-integer cycles - have fewer circuits than
the necklace population?"""
from itertools import combinations
from math import comb, gcd, ceil, log2
from collections import Counter
import statistics

def circuits(v):
    k = len(v)
    return sum(1 for p in range(k) if v[p] == 1 and v[(p-1) % k] == 0)
def canon(v):
    k = len(v)
    return min(tuple(v[j:] + v[:j]) for j in range(k))

L = log2(3)
for x in (10, 12, 15):
    k = ceil(x * L); D = 2**k - 3**x
    p3 = [3**j for j in range(x)]
    neck = {}                      # canonical word -> (gcd, circuits)
    for ds in combinations(range(k), x):
        v = [0]*k
        for d in ds: v[d] = 1
        c = canon(v)
        if c in neck: continue
        w = sum(p3[x-1-i] * 2**d for i, d in enumerate(ds))
        neck[c] = (gcd(w % D, D), circuits(list(v)))
    vals = list(neck.values())
    n = len(vals)
    mean_all = statistics.mean(c for _, c in vals)
    vals.sort(key=lambda t: -t[0])
    for topn in (10, 25, 50):
        top = vals[:topn]
        mt = statistics.mean(c for _, c in top)
        sd = statistics.pstdev([c for _, c in vals])
        z = (mt - mean_all) / (sd / topn**0.5)
        print(f"x={x:>3} k={k:>3} necklaces={n:>7}  mean circ={mean_all:.2f}  "
              f"top{topn:>3} by gcd: mean circ={mt:.2f}  z={z:+.2f}")
    print(f"        top gcds (distinct necklaces): {[g for g,_ in vals[:6]]}")
    print(f"        their circuits              : {[c for _,c in vals[:6]]}\n")
