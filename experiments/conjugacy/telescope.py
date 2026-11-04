#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Measure before cutting (lane 10): the one-step telescope for slice oscillations,
  levelOsc j (a+1) m <= levelOsc j (a+1) a + sum_{t=1}^{j} levelOsc (t-1) a m   (m <= a),
exact over all r < 2^j, j <= JMAX.  Also reports the tightness ratio and a failing control
(the inequality with the first term dropped must fail somewhere)."""
from fractions import Fraction as F
from collections import Counter
JMAX = 12
def T(x): return x // 2 if x % 2 == 0 else (3 * x + 1) // 2
vals = {}
for j in range(0, JMAX + 1):
    for r in range(2 ** j):
        x, o = r, 0
        for _ in range(j):
            o += x % 2; x = T(x)
        vals.setdefault((j, o), []).append(x)
def osc(j, a, m):
    ys = vals.get((j, a), [])
    mass = Counter(ys); cls = Counter(y % 3 ** m for y in ys)
    w = F(3 ** m, 3 ** a)
    return sum(abs(F(mass.get(y, 0)) - w * cls.get(y % 3 ** m, 0)) for y in range(3 ** a))
tests = bad = cbad = 0; worst = F(0)
for j in range(1, JMAX + 1):
    for a in range(0, j):          # slice (j, a+1)
        for m in range(0, a + 1):
            lhs = osc(j, a + 1, m)
            first = osc(j, a + 1, a)
            rest = sum(osc(t - 1, a, m) for t in range(1, j + 1))
            tests += 1
            if lhs > first + rest: bad += 1
            if lhs > rest: cbad += 1          # control: drop the first term
            if first + rest > 0: worst = max(worst, lhs / (first + rest))
print("telescope checked on", tests, "(j, a, m) triples, j <=", JMAX, "; violations:", bad)
print("control (first term dropped) violations:", cbad, "of", tests)
print("max ratio lhs/(rhs):", float(worst))
