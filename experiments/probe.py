#!/usr/bin/env -S uv run --quiet python3
"""Probe the rotation structure of Collatz cycle numerators.

Word v of length k with x ones (ones at positions d_0<...<d_{x-1}).
  W(v) = sum_i 3^(x-1-i) 2^(d_i),  D = 2^k - 3^x,  member = W(v)/D.
"""
from math import gcd
from itertools import combinations
import random

def W(v):
    k = len(v); x = sum(v)
    ds = [p for p in range(k) if v[p]]
    return sum(3**(x-1-i) * 2**d for i, d in enumerate(ds))

def rot(v, j): return v[j:] + v[:j]

def check(v):
    k = len(v); x = sum(v); D = 2**k - 3**x
    if D <= 0: return None
    out = {}
    # 1. do all rotations give unit multiples of W(v) mod D?
    inv2 = pow(2, -1, D) if D > 1 else 0
    ok = True
    for j in range(k):
        xj = sum(v[:j])
        lhs = W(rot(v, j)) % D
        rhs = (W(v) * pow(3, xj, D) * pow(inv2, j, D)) % D if D > 1 else 0
        if lhs != rhs: ok = False
    out['unit_multiple_law'] = ok
    # 2. gcd of all rotation numerators, and its gcd with D
    g = 0
    for j in range(k): g = gcd(g, W(rot(v, j)))
    out['gcd_rotations'] = g
    out['gcd_with_D'] = gcd(g, D)
    out['D'] = D
    return out

print("=== trivial cycle: word '10' (k=2, x=1) ===")
print(check([1,0]))

print("\n=== random aperiodic words, x/k near log2/log3 = 0.6309 ===")
random.seed(7)
for k in (11, 17, 23, 29, 41):
    x = round(k * 0.63093)
    if 2**k <= 3**x: x -= 1
    best = None
    for _ in range(200):
        ds = sorted(random.sample(range(k), x))
        v = [1 if p in ds else 0 for p in range(k)]
        r = check(v)
        if r and (best is None or r['gcd_rotations'] > best[1]['gcd_rotations']):
            best = (v, r)
    v, r = best
    print(f"k={k:3d} x={x:3d}  D={r['D']:<22d} unit_law={r['unit_multiple_law']}  "
          f"max gcd(rotations)={r['gcd_rotations']}  gcd(g,D)={r['gcd_with_D']}")

print("\n=== Knight's high cycle (upper Christoffel word), difference test ===")
for k in (8, 11, 19, 27):
    x = round(k*0.63093)
    if 2**k <= 3**x: x -= 1
    ds = [ (k*i)//x for i in range(x) ]
    v = [1 if p in ds else 0 for p in range(k)]
    D = 2**k - 3**x
    # the two rotations Knight compares: u01 and u10 where v_h = 1u0
    u = v[1:-1]
    a, b = W(u+[0,1]), W(u+[1,0])
    print(f"k={k:2d} x={x:2d} word={''.join(map(str,v))}  D={D:<10d} "
          f"W(u01)-W(u10)={a-b} = 2^{(a-b).bit_length()-1}? {a-b == 2**((a-b).bit_length()-1)}")
