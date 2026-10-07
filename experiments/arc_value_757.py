#!/usr/bin/env -S uv run --quiet --with pytest python3
"""The memoryless relaxed game is won at exactly beta = 7/57 (Lean: relaxedStrategy_757).

Certificate: width l = 1/8 and seven closed intervals P757 of window left ends.  solve_vw (lattice
2^-40) returns exactly this set for every beta in [7/57 - 1e-3, 7/57 - 1e-6]; its endpoints are the
rationals below.  The lattice solver rejects 7/57 itself because it drops one-point intersections;
the check here uses closed intervals, which is RelaxedStrategy's semantics.

    arc_value_757.py check      closed post-fixed-point check at 7/57 and just above
    arc_value_757.py cells      the 18 clamp cells (u = max(a, c), lift 0) used by the Lean proof
    arc_value_757.py test
"""
from __future__ import annotations

import math
import subprocess
import sys
from fractions import Fraction as F

P757 = [(F(13, 152), F(22, 171)), (F(29, 152), F(11, 57)), (F(53, 152), F(20, 57)),
        (F(565, 1368), F(79, 171)), (F(239, 456), F(10, 19)), (F(311, 456), F(13, 19)),
        (F(1021, 1368), F(15, 19))]
L = F(1, 8)
B = F(7, 57)


def cnorm(ivs):
    out = []
    for a, b in sorted((a, b) for a, b in ivs if a <= b):
        if out and a <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def cinter(A, Bs):
    return cnorm([(max(a, c), min(b, d)) for a, b in A for c, d in Bs])


def good_u(P, beta, l, d):
    """Closed set of u with [u, u + 2l/3] in an arc lift and fract(3u/2 + d) in P."""
    w = 2 * l / 3
    arc = [(k + beta, k + 1 - beta - w) for k in range(-1, 3)]
    tgt = [((J + x - d) * F(2, 3), (J + y - d) * F(2, 3)) for J in range(5) for x, y in P]
    return cinter(cnorm(arc), cnorm(tgt))


def failures(P, beta, l):
    """(d, interval) pairs where some a in the interval has no u in [a, a + l/3]."""
    bad = []
    for d in (F(0), F(1, 2)):
        acc = cnorm([(g0 - l / 3, g1) for g0, g1 in good_u(P, beta, l, d)])
        bad += [(d, iv) for iv in P if not any(a <= iv[0] and iv[1] <= b for a, b in acc)]
    return bad


def cells(P=P757, beta=B, l=L):
    """Greedy split of each (interval, d) into pieces with one clamp constant c and lift 0, as in the
    Lean lemma cell1228: s <= c <= lo + l/3, image [3c/2 + d - n, 3 hi/2 + d - n] inside one target."""
    w, out = 2 * l / 3, []
    for i, (lo, hi) in enumerate(P):
        for d in (F(0), F(1, 2)):
            p = lo
            while True:
                opts = []
                for ti, (A, Bt) in enumerate(P):
                    for n in range(3):
                        c = max(beta, (A + n - d) * F(2, 3))
                        if c <= p + l / 3 and c + w <= 1 - beta and A <= F(3, 2) * c + d - n <= Bt:
                            h = min((Bt + n - d) * F(2, 3), 1 - beta - w)
                            if h >= p:
                                opts.append((h, ti, n, c))
                if not opts:
                    raise RuntimeError(f"no cell at interval {i}, d={d}, a={p}")
                h, ti, n, c = max(opts)
                out.append((i, d, p, min(h, hi), ti, n, c))
                if h >= hi:
                    break
                p = h
    return out


def orbit_min(m0, steps, P=P757, beta=B, l=L):
    """Play the certificate against the true integer parts from m0; return min ||xi (3/2)^n||."""
    m, a, scale = m0, (P[0][0] + P[0][1]) / 2, F(1)
    for _ in range(steps):
        d = F(m % 2, 2)
        g = cinter(good_u(P, beta, l, d), [(a, a + l / 3)])
        if not g:
            raise RuntimeError("strategy stuck")
        c = F(3, 2) * g[0][0] + d
        J = math.floor(c)
        m, a, scale = (3 * m) // 2 + J, c - J, scale * F(3, 2)
    xi = (m + a) / scale
    fr = [xi * F(3, 2) ** n - math.floor(xi * F(3, 2) ** n) for n in range(steps)]
    return min(min(f, 1 - f) for f in fr)


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "check":
        for beta in (B, B + F(1, 10 ** 12)):
            print(beta, "failures:", failures(P757, beta, L))
        return 0
    if argv[0] == "cells":
        for c in cells():
            print(*c)
        return 0
    print(__doc__)
    return 2


# ---- persistent suite ----

def test_certificate_holds_at_seven_57():
    assert failures(P757, B, L) == []


def test_certificate_fails_just_above():
    # teeth: relaxed_barrier says nothing holds above 7/57, so the checker must reject this
    assert failures(P757, B + F(1, 10 ** 12), L) != []


def test_eighteen_lift0_cells():
    cs = cells()
    assert len(cs) == 18
    assert sum(1 for c in cs if c[2] != P757[c[0]][0]) == 4    # four (interval, d) pairs split once


def test_orbits_stay_seven_57_far():
    # the target 7/57 is set by hand; m0 = 100 touches it exactly
    for m0 in (1, 2, 3, 100):
        assert orbit_min(m0, 100) >= B


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
