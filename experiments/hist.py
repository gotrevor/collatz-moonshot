#!/usr/bin/env -S uv run --quiet python3
"""Where do the W(v) mod D actually land?  If 0 is avoided, is the distribution
uniform-on-nonzero, or concentrated in a coset / subgroup?"""
from itertools import combinations
from collections import Counter

def hist(k, x):
    D = 2**k - 3**x
    c = Counter()
    p3 = [3**j for j in range(x)]
    for ds in combinations(range(k), x):
        w = sum(p3[x-1-i] * 2**d for i, d in enumerate(ds))
        c[w % D] += 1
    return D, c

for k, x in ((5,3), (8,5), (11,7), (13,8), (16,10)):
    D, c = hist(k, x)
    n = sum(c.values())
    hit = sorted(c)
    print(f"\nk={k} x={x}  D={D}  words={n}  distinct residues hit={len(hit)}/{D}")
    if D <= 60:
        print(f"  residues: {hit}")
        print(f"  missed  : {[r for r in range(D) if r not in c]}")
        print(f"  counts  : {dict(sorted(c.items()))}")
    else:
        print(f"  0 hit? {0 in c}   max count on one residue: {max(c.values())}"
              f"  (uniform would be ~{n/D:.2f})")
        # is the hit set closed under multiplication by 2? by 3?
        S = set(hit)
        print(f"  closed under *2? {all((2*r) % D in S for r in hit)}"
              f"   under *3? {all((3*r) % D in S for r in hit)}")
