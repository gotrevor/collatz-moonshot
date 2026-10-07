#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Full-information survival for ||xi (3/2)^n|| >= beta: the constructor knows the integer part.

For a start interval [m, m + W) the exact interval tree keeps every component of
window ∩ (Z + [beta, 1 - beta]) and multiplies by 3/2.  survives(...) is True iff some xi in the start
interval keeps n < N far; beta_m(N) = sup of such beta (bisection) decreases in N.  Contrast: every
finite-memory relaxed game stops at 7/57 on this arc (k = 0..6 measured, k = 0 proved).

    arc_fullinfo.py scan W N M       beta_m(N) for 1 <= m < M, lowest first
    arc_fullinfo.py test
"""
from __future__ import annotations

import math
import subprocess
import sys
from fractions import Fraction as F


def comps(lo, hi, b):
    out = []
    for j in range(math.floor(lo) - 1, math.floor(hi) + 1):
        a, c = max(lo, j + b), min(hi, j + 1 - b)
        if a <= c:
            out.append((a, c))
    return out


def survives(lo, hi, b, N):
    stack = [(lo, hi, N)]
    while stack:
        lo, hi, n = stack.pop()
        if n == 0:
            return True
        stack += [(F(3, 2) * a, F(3, 2) * c, n - 1) for a, c in comps(lo, hi, b)]
    return False


def beta_m(m, W, N, it=22):
    lo, hi = F(0), F(1, 4)
    for _ in range(it):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if survives(F(m), F(m + W), mid, N) else (lo, mid)
    return lo


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "scan":
        W, N, M = int(argv[1]), int(argv[2]), int(argv[3])
        vals = sorted((float(beta_m(m, W, N)), m) for m in range(1, M))
        print("lowest:", [(m, round(v, 5)) for v, m in vals[:10]])
        print("below 7/57:", sum(1 for v, _ in vals if v < 7 / 57), "of", len(vals))
        return 0
    print(__doc__)
    return 2


# ---- persistent suite ----

def test_flp_control():
    # Flatto-Lagarias-Pollington: no orbit fits an arc shorter than 1/3, so beta = 0.34 dies everywhere
    assert not any(survives(F(m), F(m + 1), F(34, 100), 40) for m in range(1, 30))


def test_full_information_beats_seven_57():
    # 2026-10-06 measurement (tool output, recorded as a regression): at beta = 0.14 every m < 200
    # keeps some xi in [m, m + 1) far for 200 steps, against the finite-memory edge 7/57 = 0.1228
    assert all(survives(F(m), F(m + 1), F(14, 100), 200) for m in range(1, 200))


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
