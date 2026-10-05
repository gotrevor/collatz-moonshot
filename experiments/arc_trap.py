#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Parity-robust trapping of {xi (3/2)^n} in one arc [s, s+t] (exact rational interval arithmetic).

Goal: real xi > 0 whose fractional parts {xi (3/2)^n} all lie in an arc of length t.  Known: impossible
for t < 1/3 (Flatto-Lagarias-Pollington 1995); uncountably many xi for [4/65, 61/65], t = 57/65
(Pollington 1981).  Mahler's Z-numbers are the arc [0, 1/2).

Robust nested-interval strategy.  Track y = xi (3/2)^n on an interval [m + a, m + a + l] with the
fractional window [a, a + l] inside the arc.  Multiplying by 3/2 gives [1.5m + 1.5a, ...] of length
1.5 l, and 1.5m is 0 or 1/2 mod 1 according to the parity of the integer part m, which we do not
control.  So demand, for BOTH shifts d in {0, 1/2}, a new left end a' with
    [a', a' + l] inside the stretched interval  <=>  a' in [1.5a + d, 1.5a + d + l/2]  (mod 1),
and [a', a' + l] again inside the arc.  If a nonempty set P of left ends is closed under this game,
an infinite nested sequence exists for every parity history, so some xi works (and branching gives
uncountably many).  This file computes the greatest such P by iterating
    P <- P  ∩  f_0^{-1}(P - [0, l/2])  ∩  f_{1/2}^{-1}(P - [0, l/2]),   f_d(a) = 1.5 a + d mod 1.

    arc_trap.py check S T L [--iters K]   # does the arc [S, S+T] admit a robust strategy of width L?
    arc_trap.py search T [--grid G]       # scan s and l on a grid for arc length T
    arc_trap.py test
"""
from __future__ import annotations

import argparse
import subprocess
import sys
from fractions import Fraction as F

ONE = F(1)


def norm(ivs):
    """Union of closed intervals [lo, hi] inside [0, 1], merged and sorted."""
    ivs = sorted((lo, hi) for lo, hi in ivs if lo <= hi)
    out = []
    for lo, hi in ivs:
        if out and lo <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], hi))
        else:
            out.append((lo, hi))
    return out


def wrap(lo, hi):
    """The closed interval [lo, hi] (length <= 1) reduced mod 1, as intervals in [0, 1]."""
    k = (lo // 1)
    lo, hi = lo - k, hi - k
    if hi <= 1:
        return [(lo, hi)]
    return [(lo, ONE), (F(0), hi - 1)]


def circle(ivs):
    """Identify 0 ~ 1: a set containing 1 contains 0 and vice versa."""
    ivs = norm(ivs)
    if not ivs:
        return ivs
    if ivs[-1][1] == 1 and ivs[0][0] > 0:
        ivs.append((F(0), F(0)))
    if ivs[0][0] == 0 and ivs[-1][1] < 1:
        ivs.append((ONE, ONE))
    return norm(ivs)


def minus_window(P, w):
    """P - [0, w] on the circle."""
    out = []
    for lo, hi in P:
        out += wrap(lo - w, hi)
    return circle(out)


def preimage(Q, d):
    """{a in [0,1] : 1.5 a + d mod 1 in Q}."""
    out = []
    for lo, hi in Q:
        for k in range(-1, 3):  # 1.5a + d ranges over [d, 1.5 + d]
            a0, a1 = (lo + k - d) / F(3, 2), (hi + k - d) / F(3, 2)
            a0, a1 = max(a0, F(0)), min(a1, ONE)
            if a0 < a1:
                out.append((a0, a1))
    return solid(out)


def solid(ivs):
    """Left ends live on [0, 1): merge, and drop degenerate pieces (a robust strategy needs room)."""
    return [(lo, hi) for lo, hi in norm(ivs) if lo < hi]


def intersect(A, B):
    out, i, j = [], 0, 0
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if lo <= hi:
            out.append((lo, hi))
        if A[i][1] < B[j][1]:
            i += 1
        else:
            j += 1
    return norm(out)


def robust_set(s, t, l, iters=400):
    """Greatest robust set of left ends for arc [s, s+t] and window width l; [] if empty."""
    P = solid(wrap(s, s + t - l)) if t > l else []
    for _ in range(iters):
        Q = minus_window(P, l / 2)
        nxt = solid(intersect(intersect(P, preimage(Q, F(0))), preimage(Q, F(1, 2))))
        if nxt == P:
            return P, True
        P = nxt
        if not P:
            return [], True
    return P, False


def measure(P):
    return sum(hi - lo for lo, hi in P)


def main(argv):
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd")
    c = sub.add_parser("check")
    c.add_argument("s"), c.add_argument("t"), c.add_argument("l")
    c.add_argument("--iters", type=int, default=400)
    se = sub.add_parser("search")
    se.add_argument("t")
    se.add_argument("--grid", type=int, default=40)
    sub.add_parser("test")
    a = ap.parse_args(argv)
    if a.cmd == "test" or a.cmd is None:
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if a.cmd == "check":
        P, fixed = robust_set(F(a.s), F(a.t), F(a.l), a.iters)
        print(f"fixed={fixed} pieces={len(P)} measure={float(measure(P)):.6g}")
        for lo, hi in P[:20]:
            print(f"  [{lo}, {hi}]  ~ [{float(lo):.5f}, {float(hi):.5f}]")
        return 0
    if a.cmd == "search":
        t = F(a.t)
        best = None
        for i in range(a.grid):
            s = F(i, a.grid)
            for j in range(1, a.grid):
                l = t * F(j, a.grid)
                P, fixed = robust_set(s, t, l, 200)
                if P and fixed:
                    m = measure(P)
                    if best is None or m > best[0]:
                        best = (m, s, l, len(P))
        print("none" if best is None else
              f"found: s={best[1]} l={best[2]} pieces={best[3]} measure={float(best[0]):.4g}")
        return 0


# ---- persistent suite ----

def test_full_circle_is_trivially_robust():
    # arc = whole circle, any width: every left end works
    P, fixed = robust_set(F(0), ONE, F(1, 10))
    assert fixed and P


def test_short_arc_is_empty():
    # t < 1/3 is impossible for every xi (FLP Thm 1.4), so no robust strategy can exist
    for s in [F(0), F(1, 7), F(1, 3), F(1, 2)]:
        P, _ = robust_set(s, F(3, 10), F(1, 20))
        assert P == []


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
