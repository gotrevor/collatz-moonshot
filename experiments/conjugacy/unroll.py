#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Measure before cutting (lane 11): the unrolled slice telescope, for m < a,
  levelOsc j a m <= levelOsc j a (a-1) + sum_{k=m+1}^{a-1} sum_{j'<j} C(j-j'-1, a-k-1) * levelOsc j' k (k-1),
exact over all r < 2^j, j <= JMAX; controls: drop the first term (must fail), wrong weight C(j-j'-1, a-k) (must fail)."""
from fractions import Fraction as F
from collections import Counter
from math import comb
JMAX = 11
def T(x): return x // 2 if x % 2 == 0 else (3 * x + 1) // 2
vals = {}
for j in range(0, JMAX + 1):
    for r in range(2 ** j):
        x, o = r, 0
        for _ in range(j):
            o += x % 2; x = T(x)
        vals.setdefault((j, o), []).append(x)
cache = {}
def osc(j, a, m):
    key = (j, a, m)
    if key in cache: return cache[key]
    ys = vals.get((j, a), [])
    mass = Counter(ys); cls = Counter(y % 3 ** m for y in ys)
    w = F(3 ** m, 3 ** a)
    v = sum(abs(F(mass.get(y, 0)) - w * cls.get(y % 3 ** m, 0)) for y in range(3 ** a))
    cache[key] = v
    return v
tests = bad = c1 = c2 = 0; worst = F(0)
for j in range(1, JMAX + 1):
    for a in range(1, j + 1):
        for m in range(0, a):
            lhs = osc(j, a, m)
            first = osc(j, a, a - 1)
            rest = sum(comb(j - jp - 1, a - k - 1) * osc(jp, k, k - 1) for k in range(m + 1, a) for jp in range(j))
            wrong = sum(comb(j - jp - 1, a - k) * osc(jp, k, k - 1) for k in range(m + 1, a) for jp in range(j))
            tests += 1
            if lhs > first + rest: bad += 1
            if lhs > rest: c1 += 1
            if lhs > first + wrong: c2 += 1
            if first + rest > 0: worst = max(worst, lhs / (first + rest))
print("unrolled telescope checked on", tests, "(j, a, m) triples, j <=", JMAX, "; violations:", bad)
print("control 1 (first term dropped) violations:", c1, "of", tests)
print("control 2 (weight C(j-j'-1, a-k)) violations:", c2, "of", tests)
print("max ratio lhs/rhs:", float(worst))
