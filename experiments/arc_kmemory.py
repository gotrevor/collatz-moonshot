#!/usr/bin/env -S uv run --quiet --with pytest python3
"""k-memory component game for the symmetric arc [beta, 1 - beta] at a fixed rational beta.

Dominates KRelaxedStrategy (ArcTrap.lean) the way arc_barrier.py's game dominates RelaxedStrategy.
State: window W = [lo, hi] (lo in [0, 1)) and r = m mod 2^k.  The constructor keeps a component C of
W ∩ (Z + [beta, 1 - beta]); the child is 1.5 C + d (d = (r mod 2)/2), shifted by sh = floor(left end);
r' = ((3r - r mod 2)/2 + sh) mod 2^(k-1) + bit * 2^(k-1), where the adversary picks bit AFTER seeing C.
The new bit becomes a parity only k - 1 steps later, so for k >= 2 the adversary commits every parity
before the constructor's intermediate choices.  k = 1 is the memoryless game.

Measured at beta = 0.1229 from W = [0, 3], every residue: the adversary kills within 26 (k = 1),
30 (k = 2), 33 (k = 3) steps.  k = 1 reproduces the 26 of the earlier memoryless minimax.

    arc_kmemory.py kill BETA K DMAX
    arc_kmemory.py depths BETA K DMAX      per-residue kill depths
    arc_kmemory.py gaps BETA K DMAX LAYERS  extra kill depth one more step of delay costs, per state
    arc_kmemory.py test
"""
from __future__ import annotations

import math
import subprocess
import sys
from fractions import Fraction as F
from functools import lru_cache

sys.setrecursionlimit(100000)
H = F(1, 2)


def make(beta, k):
    half = 1 << (k - 1)

    @lru_cache(maxsize=None)
    def children(lo, hi, r):
        d = H if r % 2 else F(0)
        out = []
        for j in range(math.floor(lo) - 1, math.floor(hi) + 1):
            a, b = max(lo, j + beta), min(hi, j + 1 - beta)
            if a <= b:
                nl, nh = F(3, 2) * a + d, F(3, 2) * b + d
                sh = math.floor(nl)
                base = ((3 * r - r % 2) // 2 + sh) % half if half > 1 else 0
                out.append((nl - sh, nh - sh, base))
        return tuple(out)

    @lru_cache(maxsize=None)
    def adv(lo, hi, r, D):
        """The adversary forces death within D steps."""
        if D == 0:
            return False
        return all(any(adv(nl, nh, base + bit * half, D - 1) for bit in (0, 1))
                   for nl, nh, base in children(lo, hi, r))

    return adv


def kill_depth(beta, k, dmax):
    """Least D such that the adversary kills every residue from [0, 3] within D steps, else None."""
    adv = make(beta, k)
    for D in range(1, dmax + 1):
        if all(adv(F(0), F(3), r, D) for r in range(1 << k)):
            return D
    return None


def residue_depths(beta, k, dmax):
    """Per residue r < 2^k: least D such that the adversary kills [0, 3] at r within D (None if > dmax)."""
    adv = make(beta, k)
    out = []
    for r in range(1 << k):
        out.append(next((D for D in range(1, dmax + 1) if adv(F(0), F(3), r, D)), None))
    return out


def make_children(beta, k):
    half = 1 << (k - 1)

    def children(lo, hi, r):
        d = H if r % 2 else F(0)
        out = []
        for j in range(math.floor(lo) - 1, math.floor(hi) + 1):
            a, b = max(lo, j + beta), min(hi, j + 1 - beta)
            if a <= b:
                nl, nh = F(3, 2) * a + d, F(3, 2) * b + d
                sh = math.floor(nl)
                base = ((3 * r - r % 2) // 2 + sh) % half if half > 1 else 0
                out.append((nl - sh, nh - sh, base))
        return out

    return children


def delay_gaps(beta, k, dmax, layers):
    """Cost of one more step of delay, state by state.  Over the (k+1)-game states reachable from
    ([0, 3], r) within `layers` moves (any constructor component, either adversary bit), compare the
    kill depth d1 in the (k+1)-game with d0 at the projected k-state (window, r mod 2^k) in the k-game.
    Returns {d1 - d0: count}, with 'k+1 survives' counting states killable in the k-game but not
    within dmax in the (k+1)-game."""
    adv0, adv1 = make(beta, k), make(beta, k + 1)
    ch1 = make_children(beta, k + 1)
    half1 = 1 << k

    def depth(adv, st):
        return next((D for D in range(1, dmax + 1) if adv(*st, D)), None)

    seen = set()
    frontier = [(F(0), F(3), r) for r in range(1 << (k + 1))]
    for _ in range(layers + 1):
        nxt = []
        for st in frontier:
            if st in seen:
                continue
            seen.add(st)
            for nl, nh, base in ch1(*st):
                nxt += [(nl, nh, base + bit * half1) for bit in (0, 1)]
        frontier = nxt
    hist = {}
    for lo, hi, r in seen:
        d0 = depth(adv0, (lo, hi, r % (1 << k)))
        if d0 is None:
            continue
        d1 = depth(adv1, (lo, hi, r))
        key = "k+1 survives" if d1 is None else d1 - d0
        hist[key] = hist.get(key, 0) + 1
    return dict(sorted(hist.items(), key=str))


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "kill":
        print(kill_depth(F(argv[1]), int(argv[2]), int(argv[3])))
        return 0
    if argv[0] == "gaps":
        print(delay_gaps(F(argv[1]), int(argv[2]), int(argv[3]), int(argv[4])))
        return 0
    if argv[0] == "depths":
        print(residue_depths(F(argv[1]), int(argv[2]), int(argv[3])))
        return 0
    print(__doc__)
    return 2


# ---- persistent suite ----

def test_memoryless_depth_matches_earlier_minimax():
    # 26 at beta = 0.1229 was measured by an independent minimax on 2026-10-05 (ArcTrap docstring)
    assert kill_depth(F(1229, 10000), 1, 40) == 26


def test_two_bits_still_killed():
    assert kill_depth(F(1229, 10000), 2, 40) == 30


def test_below_edge_not_killed():
    # teeth: below 7/57 the constructor wins (relaxedStrategy_757), so no kill may appear within the
    # depth that kills at 0.1229 (a deeper search here grows without bound)
    assert kill_depth(F(7, 57) - F(1, 1000), 1, 26) is None


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
