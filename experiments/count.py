#!/usr/bin/env -S uv run --quiet python3
"""Every binary word (k letters, x ones) is the parity word of exactly one
rational cycle, with minimum-ish member W(v)/D, D = 2^k - 3^x.  It is an INTEGER
cycle iff D | W(v).

Naive heuristic: #words / D solutions expected.  Does reality match?
If reality is systematically BELOW the heuristic, the values W(v) mod D avoid 0
structurally, and that structure is the theorem to hunt."""
from itertools import combinations
from math import comb

print(f"{'k':>3} {'x':>3} {'D':>12} {'#words':>10} {'expected':>10} {'actual':>7}")
tot_exp = tot_act = 0.0
for k in range(2, 21):
    for x in range(1, k):
        D = 2**k - 3**x
        if D <= 0: continue
        n = comb(k, x)
        exp = n / D
        act = 0
        p3 = [3**j for j in range(x)]
        p2 = [pow(2, p, D) for p in range(k)]
        for ds in combinations(range(k), x):
            w = 0
            for i, d in enumerate(ds):
                w += p3[x-1-i] * p2[d]
            if w % D == 0: act += 1
        tot_exp += exp; tot_act += act
        if act or exp > 0.5:
            print(f"{k:>3} {x:>3} {D:>12} {n:>10} {exp:>10.3f} {act:>7}")
print(f"\nTOTALS over 2<=k<=20:  expected {tot_exp:.2f}   actual {tot_act:.0f}")
