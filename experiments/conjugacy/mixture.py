# Check of the slice mixture identity behind the sliced telescope (SliceOscCentral.lean,
# `sliceOscDecayCentral_of_sliceOscStep`):
#   levelClass j a a' c = sum_{t=1}^{j} C(j-t, a-a'-1) * levelMass (t-1) a' c   (a' < a, c < 3^a')
# i.e. reducing the slice (j, a) mod 3^a' gives a binomially weighted sum of the slices (t-1, a').
# Exact over all r < 2^j, j <= 13.  Usage: python3 -I mixture.py
from math import comb
def T(x): return x // 2 if x % 2 == 0 else (3 * x + 1) // 2
JMAX = 13
vals = {}  # (j, a) -> list of T^j r over the slice
for j in range(0, JMAX + 1):
    for r in range(2 ** j):
        x, o = r, 0
        for _ in range(j):
            o += x % 2
            x = T(x)
        vals.setdefault((j, o), []).append(x)
def hist(j, a, mod):
    h = [0] * mod
    for y in vals.get((j, a), []): h[y % mod] += 1
    return h
tests = bad = 0
for j in range(1, JMAX + 1):
    for a in range(1, j + 1):
        for ap in range(0, a):
            M = 3 ** ap
            lhs = hist(j, a, M)
            rhs = [0] * M
            for t in range(1, j + 1):
                w = comb(j - t, a - ap - 1)
                if w:
                    h = hist(t - 1, ap, M)
                    for c in range(M): rhs[c] += w * h[c]
            tests += 1
            if lhs != rhs: bad += 1
print('identity checked on', tests, "(j, a, a') triples, j <=", JMAX, '; mismatches:', bad)
# Control: the same check with the weight C(j-t, a-a') (off by one) must fail.
cbad = 0
for j in range(1, JMAX + 1):
    for a in range(1, j + 1):
        for ap in range(0, a):
            M = 3 ** ap
            lhs = hist(j, a, M)
            rhs = [0] * M
            for t in range(1, j + 1):
                w = comb(j - t, a - ap)
                if w:
                    h = hist(t - 1, ap, M)
                    for c in range(M): rhs[c] += w * h[c]
            if lhs != rhs: cbad += 1
print('control (weight C(j-t, a-a\')): mismatches', cbad, 'of', tests)
