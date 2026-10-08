#!/usr/bin/env -S uv run --quiet --with pytest python3
"""A k-independent adversary for the delay-k digit game: does one simple rule kill every lookahead?

Game (the component game of arc_kmemory.py, in xi coordinates).  xi = m + f, f in [0, 3), m's binary
digits chosen by the adversary.  The cut at time s keeps f with fract((m + f)(3/2)^s) in [beta, 1 - beta];
it depends on the digits below s only.  At time t the constructor keeps one component I_t of the cut,
knowing the digits below t + k (the first k are a given prefix, as arc_kmemory quantifies over every
residue).  Then the adversary chooses digit t + k, seeing I_t.

Greedy adversary: choose the digit minimising the measure (in f) of the cone, the oblivious tree from
I_t through cuts t + 1 .. t + k + 1 under the committed digits.  The constructor is exact: a DFS over its
component choices against the now-deterministic adversary.  greedy_depth = the first time by which every
constructor line has died, maximised over prefixes; None if some line reaches the horizon T.

    arc_greedy.py depth BETA K T [POT [EXTRA]]   greedy kill depth (max over the 2^K prefixes);
                                               POT in measure, count, max, sqrt
    arc_greedy.py test
"""
from __future__ import annotations

import math
import subprocess
import sys
from fractions import Fraction as F


def cut(a, b, m, s, beta):
    """Components of {f in [a, b] : fract((m + f)(3/2)^s) in [beta, 1 - beta]}."""
    g = F(3 ** s, 2 ** s)
    base = F((m % (1 << s)) * 3 ** s, 1 << s) if s else F(0)
    lo, hi = base + a * g, base + b * g
    out = []
    for j in range(math.floor(lo) - 1, math.floor(hi) + 1):
        x, y = max(lo, j + beta), min(hi, j + 1 - beta)
        if x <= y:
            out.append(((x - base) / g, (y - base) / g))
    return out


POT = {"measure": lambda ls: sum(ls), "count": len, "max": max,
       "sqrt": lambda ls: sum(float(x) ** 0.5 for x in ls)}


def cone_measure(a, b, m, t, k, beta, pot="measure", extra=0):
    """Potential of the oblivious tree from [a, b] (kept at time t) after cuts t + 1 .. t + k + 1 + extra
    (`extra` > 0 looks past the committed digits, minimising over the unknown ones)."""
    ivs = [(a, b)]
    for s in range(t + 1, t + k + 2):
        ivs = [c for x, y in ivs for c in cut(x, y, m, s, beta)]
        if not ivs:
            return 0
    if extra:
        return min(cone_measure_from(ivs, m + (d << (t + k + 1)), t + k + 1, beta, pot, extra - 1)
                   for d in (0, 1))
    return POT[pot]([y - x for x, y in ivs])


def cone_measure_from(ivs, m, s0, beta, pot, extra):
    ivs = [c for x, y in ivs for c in cut(x, y, m, s0 + 1, beta)]
    if not ivs:
        return 0
    if extra:
        return min(cone_measure_from(ivs, m + (d << (s0 + 1)), s0 + 1, beta, pot, extra - 1) for d in (0, 1))
    return POT[pot]([y - x for x, y in ivs])


def survive_depth(beta, k, T, prefix, pot="measure", extra=0):
    """Deepest time any constructor line reaches against the greedy adversary (T = survived)."""
    best = -1

    def dfs(t, a, b, m):
        nonlocal best
        best = max(best, t)
        if t >= T:
            return True
        bit = min((0, 1), key=lambda d: cone_measure(a, b, m + (d << (t + k)), t, k, beta, pot, extra))
        m2 = m + (bit << (t + k))
        return any(dfs(t + 1, x, y, m2) for x, y in cut(a, b, m2, t + 1, beta))

    for x, y in cut(F(0), F(3), prefix, 0, beta):
        if dfs(0, x, y, prefix):
            return T
    return best


def greedy_depth(beta, k, T, pot="measure", extra=0):
    """Kill depth of the greedy adversary, maximised over prefixes; None if a line survives to T."""
    worst = 0
    for p in range(1 << k):
        d = survive_depth(beta, k, T, p, pot, extra)
        if d >= T:
            return None
        worst = max(worst, d + 1)
    return worst


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "depth":
        pot = argv[4] if len(argv) > 4 else "measure"
        extra = int(argv[5]) if len(argv) > 5 else 0
        print(greedy_depth(F(argv[1]), int(argv[2]), int(argv[3]), pot, extra))
        return 0
    print(__doc__)
    return 2


# ---- persistent suite ----

def test_cut_by_hand():
    # s = 0, m = 0: f in [0, 3) keeps [1/8, 7/8], [9/8, 15/8], [17/8, 23/8]
    assert cut(F(0), F(3), 0, 0, F(1, 8)) == [(F(1, 8), F(7, 8)), (F(9, 8), F(15, 8)), (F(17, 8), F(23, 8))]
    # s = 1, m = 1: (1 + f) 3/2 on f in [0, 1/2] is [3/2, 9/4]; keeps [3/2, 15/8] and [17/8, 9/4],
    # i.e. f in [0, 1/4] and [5/12, 1/2]
    assert cut(F(0), F(1, 2), 1, 1, F(1, 8)) == [(F(0), F(1, 4)), (F(5, 12), F(1, 2))]


def test_greedy_no_better_than_exact():
    # the exact adaptive adversary (arc_kmemory, D(1) = 14 at 0.13) is optimal, so greedy needs >= 14
    d = greedy_depth(F(13, 100), 1, 60)
    assert d is None or d >= 14


def test_below_edge_greedy_fails():
    # teeth: below 7/57 the constructor survives everything (relaxedStrategy_757)
    assert greedy_depth(F(12, 100), 1, 40) is None


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
