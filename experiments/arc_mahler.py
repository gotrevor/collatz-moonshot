#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Mahler's arc is out of reach of adversarial-parity constructions: an exact proof for every position.

Same component game as arc_barrier.py (it dominates every memoryless relaxed strategy), but the arc is
[s, s + 1/2] with the POSITION s as the symbol.  Every window endpoint is affine in s.

Claim: for every s in [0, 1) the adversary kills every constructor path within DEPTH moves.  Since any
arc of length <= 1/2 sits inside such an arc, no memoryless adversarial-parity strategy holds ANY arc of
length <= 1/2 -- in particular not Mahler's [0, 1/2).

Hand proof for length t < 1/2 (no computer; RESEARCH note): the arc A and A + 1/2 are disjoint, so the
adversary can always keep at most half of 1.5|C| in the arc (|C| shrinks by 3/4 per move), and once the
window is shorter than 1/2 - t it misses A or A - 1/2 entirely.

    arc_mahler.py verify
    arc_mahler.py test
"""
from __future__ import annotations

import subprocess
import sys
from fractions import Fraction as F

from arc_barrier import Aff, Split, cmp, floor_on

H = F(1, 2)
S = Aff(0, 1)           # the symbol: here it is the arc position s, not beta
T = F(1, 2)
DEPTH = 5


def children(w, d, lo, hi, t=T):
    wl, wh = w
    out = {}
    for k in range(floor_on(wl, lo, hi) - 2, floor_on(wh, lo, hi) + 2):
        a = wl if cmp(wl, S + k, lo, hi) >= 0 else S + k
        b = wh if cmp(wh, S + (k + t), lo, hi) <= 0 else S + (k + t)
        if cmp(a, b, lo, hi) < 0:
            nl, nh = a.scale(F(3, 2)) + d, b.scale(F(3, 2)) + d
            sh = floor_on(nl, lo, hi)
            nl, nh = nl - sh, nh - sh
            out[(nl.key(), nh.key())] = (nl, nh)
    return list(out.values())


def kills(lo, hi, depth=DEPTH, t=T):
    """True if for every s in the open interval (lo, hi) the adversary kills within depth moves."""
    memo = {}

    def win(w, k):
        key = (w[0].key(), w[1].key(), k)
        if key not in memo:
            memo[key] = k > 0 and any(all(win(c, k - 1) for c in children(w, d, lo, hi, t))
                                      for d in (F(0), H))
        return memo[key]

    return win((S, S + t), depth)


def point_kills(s, depth=DEPTH, t=T):
    """Exact check at a single s (split points and the endpoint s = 0)."""
    def comps(lo, hi):
        out = []
        for k in range(int(lo // 1) - 2, int(hi // 1) + 2):
            a, b = max(lo, k + s), min(hi, k + s + t)
            if a < b:
                out.append((a, b))
        return out

    memo = {}

    def win(lo, hi, k):
        if (lo, hi, k) not in memo:
            memo[(lo, hi, k)] = k > 0 and any(
                all(win(*nrm(F(3, 2) * a + d, F(3, 2) * b + d), k - 1) for a, b in comps(lo, hi))
                for d in (F(0), H))
        return memo[(lo, hi, k)]

    def nrm(x, y):
        sh = x // 1
        return x - sh, y - sh

    return win(s, s + t, depth)


def verify(lo=F(0), hi=F(1), depth=DEPTH, t=T):
    todo, pieces, points, ok = [(lo, hi)], 0, {lo}, True
    while todo:
        a, b = todo.pop()
        try:
            ok = kills(a, b, depth, t) and ok
            pieces += 1
        except Split as sp:
            assert a < sp.at < b, (a, sp.at, b)
            points.add(sp.at)
            todo += [(a, sp.at), (sp.at, b)]
    ok = all(point_kills(x, depth, t) for x in points) and ok
    return ok, pieces, len(points)


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "verify":
        ok, n, m = verify()
        print(f"every arc [s, s+1/2], s in [0,1), killed within {DEPTH} moves: {ok}  "
              f"({n} open s-pieces, {m} exact points)")
        return 0 if ok else 1
    print(__doc__)
    return 2


# ---- persistent suite ----

def test_mahler_arc_killed_everywhere():
    ok, _, _ = verify()
    assert ok


def test_hand_mahler_arc_depth():
    # Mahler's [0, 1/2], by hand: d = 1/2 sends the start [0, 1/2] to [1/2, 5/4] whose only
    # arc parts are the point 1/2 and [1, 5/4]; d = 0 sends it to [0, 3/4] -> part [0, 1/2].
    # So the adversary cannot kill in one move (it must play on): depth 1 fails.
    assert not point_kills(F(0), 1)
    assert point_kills(F(0), DEPTH)


def test_teeth_long_arc_not_killed():
    # a long arc must NOT be killable: the relaxed game holds [beta, 1 - beta] for beta = 0.12
    assert not point_kills(F(12, 100), 8, F(76, 100))


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
