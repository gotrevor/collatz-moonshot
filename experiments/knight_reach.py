#!/usr/bin/env -S uv run --quiet python3
"""How far does Knight's trick reach?  (Thread 2, FRONT-B-ROUTES.md)

Knight (2026) kills high cycles because two rotations of the upper Christoffel word
have numerator difference EXACTLY 2^(k-2): integrality forces D | diff, D is odd and
coprime to 3, so D = +-1, and elementary arithmetic finishes.  The trick therefore
fires on ANY word where some rotation pair's numerator difference is +-2^s * 3^t.

This probe computes the exact reach: for every primitive necklace (canonical rotation
representative) of length k <= K, does some rotation pair fire?  And is the firing
class exactly the balanced (Sturmian/Christoffel) words - the Morse-Hedlund heuristic
in the route map - or bigger?

Conventions match CollatzMoonshot/FrontB/Words.lean:
  numer(false :: t) = 2*numer(t);  numer(true :: t) = 2*numer(t) + 3^ones(t)
  den(v) = 2^len - 3^ones  (sign kept: negative D = the 3n-1 mirror, cycles exist)
  rotation recurrence (Words.lean two_mul_numer_rot_*):
    head false: 2*M(rot v) = M(v)         head true: 2*M(rot v) = 3*M(v) + D
"""

import sys
from math import gcd

K_MAX = int(sys.argv[1]) if len(sys.argv) > 1 else 18


def ones(v):
    return sum(v)


def numer(v):
    m = 0
    x = 0  # ones of the tail seen so far, scanning from the right
    for b in reversed(v):
        if b:
            m = 2 * m + 3**x
            x += 1
        else:
            m = 2 * m
    return m


def rotation_numerators(v, D):
    """M for every rotation, via the exact recurrence; verified vs numer() below."""
    k = len(v)
    ms = [numer(v)]
    for i in range(k - 1):
        m = ms[-1]
        if v[i]:
            m2, r = divmod(3 * m + D, 2)
        else:
            m2, r = divmod(m, 2)
        assert r == 0
        ms.append(m2)
    return ms


def strip23(n):
    n = abs(n)
    while n % 2 == 0:
        n //= 2
    while n % 3 == 0:
        n //= 3
    return n


def canonical(v):
    k = len(v)
    return min(tuple(v[i:] + v[:i]) for i in range(k))


def is_primitive(v):
    k = len(v)
    for d in range(1, k):
        if k % d == 0 and v == v[d:] + v[:d]:
            return False
    return True


def is_cyclically_balanced(v):
    """Balanced: cyclic factors of equal length have ones-counts differing <= 1."""
    k = len(v)
    w = v + v
    for L in range(1, k):
        counts = [sum(w[i : i + L]) for i in range(k)]
        if max(counts) - min(counts) > 1:
            return False
    return True


def upper_christoffel(x, k):
    """Upper mechanical word: v[i] = ceil((i+1)*x/k) - ceil(i*x/k), as booleans."""
    return [bool(-((-(i + 1) * x) // k) - (-(-(i * x) // k))) for i in range(k)]


# sanity: recurrence matches direct numer on all words of length <= 10
for k in range(1, 11):
    for bits in range(2**k):
        v = [(bits >> i) & 1 == 1 for i in range(k)]
        D = 2**k - 3 ** ones(v)
        ms = rotation_numerators(v, D)
        for i in range(k):
            assert ms[i] == numer(v[i:] + v[:i]), (v, i)
print("recurrence sanity: OK (exhaustive k <= 10)")

# sanity: Knight's own case fires with a pure 2-power difference
for x, k in [(3, 5), (4, 7), (5, 8), (7, 12)]:
    v = upper_christoffel(x, k)
    assert ones(v) == x
    D = 2**k - 3**x
    ms = rotation_numerators(v, D)
    fired = any(
        strip23(ms[i] - ms[j]) == 1
        for i in range(k)
        for j in range(i + 1, k)
        if ms[i] != ms[j]
    )
    assert fired, (x, k)
print("Knight in-family sanity: upper Christoffel words fire. OK")

print(f"\nsweep: primitive necklaces, 1 <= ones < k, k <= {K_MAX}")
print("word classes among FIRING words (D>0 side and D<0 mirror):\n")

total = fired_n = 0
firing_unbalanced = []
firing_balanced_pos = []
zero_diff_words = []
per_k = {}

for k in range(2, K_MAX + 1):
    seen = set()
    kf = kt = 0
    for bits in range(1, 2**k - 1):
        v = tuple((bits >> i) & 1 == 1 for i in range(k))
        if canonical(list(v)) != v:
            continue
        lv = list(v)
        if not is_primitive(lv):
            continue
        x = ones(lv)
        D = 2**k - 3**x
        if D == 0:
            continue
        total += 1
        kt += 1
        ms = rotation_numerators(lv, D)
        pairs = [
            (i, j)
            for i in range(k)
            for j in range(i + 1, k)
            if ms[i] != ms[j] and strip23(ms[i] - ms[j]) == 1
        ]
        if any(ms[i] == ms[j] for i in range(k) for j in range(i + 1, k)):
            zero_diff_words.append((k, x, v))
        if pairs:
            fired_n += 1
            kf += 1
            bal = is_cyclically_balanced(lv)
            if not bal:
                firing_unbalanced.append((k, x, D, v, pairs[:2]))
            elif D > 0:
                firing_balanced_pos.append((k, x, D, v, len(pairs)))
    per_k[k] = (kf, kt)

print(f"{'k':>3} {'fired':>6} {'primitive':>10}")
for k, (kf, kt) in per_k.items():
    print(f"{k:>3} {kf:>6} {kt:>10}")
print(f"\ntotal primitive necklaces: {total}, firing: {fired_n}")
print(f"zero-diff rotation pairs (distinct rotations, equal numerator): {len(zero_diff_words)}")

print(f"\nFIRING UNBALANCED words (beyond the Morse-Hedlund heuristic): {len(firing_unbalanced)}")
for k, x, D, v, ps in firing_unbalanced[:25]:
    w = "".join("1" if b else "0" for b in v)
    print(f"  k={k:2d} x={x:2d} D={D:12d}  {w}  pairs~{ps}")

print(f"\nfiring balanced with D > 0 (Knight/Steiner territory): {len(firing_balanced_pos)}")
for k, x, D, v, np_ in firing_balanced_pos[:25]:
    w = "".join("1" if b else "0" for b in v)
    print(f"  k={k:2d} x={x:2d} D={D:8d}  {w}  ({np_} firing pairs)")
