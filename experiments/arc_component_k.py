#!/usr/bin/env -S uv run --quiet --with pytest python3
"""k-memory component game (`ArcDelayGame.KComponentStrategy`): exact AND-OR kill depth.

A state is a window [x, y] of positions X = xi (3/2)^n, kept modulo 2^k.  The constructor keeps one
component of the window inside an arc lift [j + beta, j + 1 - beta]; its image under 3/2 is known modulo
2^(k-1) and the adversary picks the top bit.  k = 1 is the component game of `ArcTrap.relaxed_barrier`.
No window width: this game dominates every fixed-width k-memory relaxed strategy.

    arc_component_k.py depth K BETA MAXDEPTH    first depth at which every start residue dies (or None)
    arc_component_k.py test
"""
from __future__ import annotations

import subprocess
import sys
from fractions import Fraction as F
from functools import lru_cache


def kill_depth(k, beta, max_depth):
    """(first depth at which every start r + arc dies, or None; memo size)."""
    Mh = 2 ** (k - 1)
    s, e = F(beta), 1 - F(beta)

    @lru_cache(maxsize=None)
    def surv(x, y, d):
        if d == 0:
            return True
        for j in range(int(x // 1) - 1, int(y // 1) + 1):
            a, b = max(x, j + s), min(y, j + e)
            if a < b:
                na, nb = F(3, 2) * a, F(3, 2) * b
                sh = (na // Mh) * Mh
                if all(surv(na - sh + t * Mh, nb - sh + t * Mh, d - 1) for t in (0, 1)):
                    return True
        return False

    for dd in range(1, max_depth + 1):
        if not any(surv(F(r) + s, F(r) + e, dd) for r in range(2 ** k)):
            return dd, surv.cache_info().currsize
    return None, surv.cache_info().currsize


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "depth":
        print(kill_depth(int(argv[1]), F(argv[2]), int(argv[3])))
        return 0
    print(__doc__)
    return 2


# ---- persistent suite ----

def test_component_game_dies_above_threshold():
    """beta = 0.13: every start dies at depth 14 (k = 1) and 16 (k = 2)."""
    assert kill_depth(1, F(13, 100), 30)[0] == 14
    assert kill_depth(2, F(13, 100), 30)[0] == 16


def test_component_game_survives_below_threshold():
    """Known-answer control: at beta = 3/25 < 7/57 a memoryless relaxed strategy exists, so it survives."""
    assert kill_depth(1, F(3, 25), 20)[0] is None
    assert kill_depth(2, F(3, 25), 16)[0] is None


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
