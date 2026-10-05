#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Exact minimax for the adversarial-parity arc game: does ANY strategy survive?

Upper-bound companion to arc_trap_k.py.  Bigger windows dominate, so the constructor's best move is a
whole component of W ∩ (lifts of the arc [beta, 1 - beta]); starting from the full arc dominates
every start.  One step: the constructor knows the next LOOKAHEAD parities (the adversary commits each
new parity LOOKAHEAD steps ahead), picks a component C, and the window becomes 1.5 C + d (mod 1).
Depth counts moves, the first being the start arc.  "dies at depth D" is an exact proof that no such strategy survives D steps, for that beta.

    arc_minimax.py depth BETA LOOKAHEAD MAXD
    arc_minimax.py test
"""
from __future__ import annotations

import subprocess
import sys
from fractions import Fraction as F
from functools import lru_cache
from itertools import product

HALF, THREE_HALVES = F(1, 2), F(3, 2)


def make(beta):
    s, e = beta, 1 - beta

    def comps(lo, hi):
        out = []
        for k in range(int(lo // 1) - 1, int(hi // 1) + 2):
            a, b = max(lo, k + s), min(hi, k + e)
            if a < b:
                out.append((a, b))
        return out

    @lru_cache(maxsize=None)
    def survive(lo, hi, q, depth):
        if depth == 0:
            return True
        d = q[0]
        for nd in (F(0), HALF):
            ok = False
            for a, b in comps(lo, hi):
                nlo, nhi = THREE_HALVES * a + d, THREE_HALVES * b + d
                sh = nlo // 1
                if survive(nlo - sh, nhi - sh, q[1:] + (nd,), depth - 1):
                    ok = True
                    break
            if not ok:
                return False
        return True

    return s, e, survive


def death_depth(beta, lookahead, maxd):
    """Smallest depth at which every strategy (and every initial known parity string) is forced out,
    or None if some strategy survives maxd steps."""
    s, e, survive = make(beta)
    for D in range(1, maxd + 1):
        if not any(survive(s, e, q, D) for q in product((F(0), HALF), repeat=lookahead)):
            return D
    return None


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "depth":
        beta, la, maxd = F(argv[1]), int(argv[2]), int(argv[3])
        D = death_depth(beta, la, maxd)
        print(f"beta={beta} lookahead={la}: " + (f"dies at depth {D}" if D else f"survives depth {maxd}"))
        return 0
    print(__doc__)
    return 2


# ---- persistent suite ----

def test_hand_computed_short_arc_dies_at_once():
    # [0.4, 0.6]: move 1 takes the whole arc; then d = 0 gives 1.5W = [0.6, 0.9] and d = 1/2 gives
    # [1.1, 1.4], each meeting the arc's lifts only in a point, so move 2 is impossible (by hand)
    assert death_depth(F(2, 5), 1, 5) == 2


def test_below_seven_fifty_sevenths_survives():
    # the relaxed game wins at 0.12 (arc_trap_k certificates), so the dominating game cannot die
    assert death_depth(F(12, 100), 1, 14) is None


def test_barrier_depths_regression():
    # exact minimax output, recorded 2026-10-05 (regression, not ground truth)
    assert death_depth(F(15, 100), 1, 20) == 11
    assert death_depth(F(13, 100), 2, 30) == 18


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
