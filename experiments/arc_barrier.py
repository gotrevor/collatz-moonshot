#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Barrier at 7/57 for the memoryless adversarial-parity arc game, verified symbolically in beta.

Game (it dominates every memoryless relaxed strategy, `RelaxedStrategy` in ArcTrap.lean): the window W
starts as the arc [beta, 1 - beta]; each step the adversary picks the parity d in {0, 1/2} (it may
look at W), the constructor keeps any component C of W ∩ (arc lifts), and W becomes 1.5 C + d,
normalised mod 1.  Because d is chosen fresh each step, integer shifts of W are irrelevant and a
smaller window is never better than a larger one.

Claim: for every beta > 7/57 the adversary wins (every constructor path dies).
  (a) beta in (7/57, 0.1229]: an adaptive adversary forces every branch, within FUNNEL_DEPTH moves,
      either to die or to reach a window inside [x0, R0] with x0 > 10/19, where R0 = 1 - 9 beta/4.
      Checked here by an AND-OR search whose window endpoints are affine in beta (exact, open at 7/57).
  (b) Runaway lemma (hand proof, RESEARCH note): for beta in (0.1143, 4/19), the block (0, 1/2, 1/2)
      maps a window [x, R0] with x > 10/19 to [g(x), R0] with g(x) = 27x/8 - 5/4, or kills it.
      g repels from its fixed point 10/19 by 27/8, so finitely many blocks kill.
  (c) beta > 0.1229: the arc shrinks as beta grows, so the 0.1229 strategy, played against the
      larger shadow window, still kills.
The threshold enters only through the funnel: the arc's left edge, after two 1/2-steps, lands at
9 beta/4 + 1/4, which exceeds 10/19 exactly when beta > 7/57.

    arc_barrier.py verify
    arc_barrier.py test
"""
from __future__ import annotations

import subprocess
import sys
from fractions import Fraction as F

H = F(1, 2)
BETA_EDGE, BETA_SPLIT = F(7, 57), F(1229, 10000)
FUNNEL_DEPTH = 13


class Aff:
    """a + b*beta"""
    __slots__ = ("a", "b")

    def __init__(self, a, b=F(0)):
        self.a, self.b = F(a), F(b)

    def __add__(self, o):
        o = o if isinstance(o, Aff) else Aff(o)
        return Aff(self.a + o.a, self.b + o.b)

    def __sub__(self, o):
        o = o if isinstance(o, Aff) else Aff(o)
        return Aff(self.a - o.a, self.b - o.b)

    def scale(self, c):
        return Aff(self.a * c, self.b * c)

    def at(self, x):
        return self.a + self.b * x

    def key(self):
        return (self.a, self.b)


BETA = Aff(0, 1)


def sign_on(f, lo, hi):
    """Sign of f on the OPEN interval (lo, hi), or None if it changes sign inside."""
    def side(v, toward):          # sign just inside an endpoint where f may vanish
        return (v > 0) - (v < 0) if v != 0 else toward
    sb = (f.b > 0) - (f.b < 0)
    s_lo, s_hi = side(f.at(lo), sb), side(f.at(hi), -sb)
    return s_lo if s_lo == s_hi else None


def root(f):
    return -f.a / f.b


class Split(Exception):
    def __init__(self, at):
        self.at = at


def cmp(f, g, lo, hi):
    s = sign_on(f - g, lo, hi)
    if s is None:
        raise Split(root(f - g))
    return s


def floor_on(f, lo, hi):
    """floor(f) constant on (lo, hi); split at an integer crossing otherwise."""
    k = (f.at((lo + hi) / 2)).__floor__()
    # f >= k and f < k + 1 on the open interval (lo, hi)
    if cmp(f, Aff(k), lo, hi) < 0:
        raise Split(root(f - Aff(k)))
    if cmp(f, Aff(k + 1), lo, hi) >= 0:
        raise Split(root(f - Aff(k + 1)))
    return k


def children(w, d, lo, hi):
    """Normalised child windows of w under parity d, one per component."""
    wl, wh = w
    out = {}
    for k in range(floor_on(wl, lo, hi) - 1, floor_on(wh, lo, hi) + 2):
        a = wl if cmp(wl, BETA + k, lo, hi) >= 0 else BETA + k
        b = wh if cmp(wh, Aff(k + 1) - BETA, lo, hi) <= 0 else Aff(k + 1) - BETA
        if cmp(a, b, lo, hi) < 0:
            nl, nh = a.scale(F(3, 2)) + d, b.scale(F(3, 2)) + d
            sh = floor_on(nl, lo, hi)
            nl, nh = nl - sh, nh - sh
            out[(nl.key(), nh.key())] = (nl, nh)
    return list(out.values())


def clean(w, lo, hi):
    R0 = Aff(1) - BETA.scale(F(9, 4))
    return cmp(w[0], Aff(F(10, 19)), lo, hi) > 0 and cmp(w[1], R0, lo, hi) <= 0


def funnel(lo, hi, depth=FUNNEL_DEPTH):
    """True if, for every beta in (lo, hi], the adversary forces clean-or-dead within depth moves.
    Raises Split if a comparison changes sign inside the open interval (lo, hi)."""
    memo = {}

    def win(w, k):
        key = (w[0].key(), w[1].key(), k)
        if key in memo:
            return memo[key]
        r = clean(w, lo, hi) or (k > 0 and any(all(win(c, k - 1) for c in children(w, d, lo, hi))
                                                for d in (F(0), H)))
        memo[key] = r
        return r

    return win((BETA, Aff(1) - BETA), depth)


def point_funnel(beta, depth=FUNNEL_DEPTH):
    """Exact check at a single beta (used for the finitely many split points)."""
    s0, e0, R0, X = beta, 1 - beta, 1 - F(9, 4) * beta, F(10, 19)

    def comps(lo, hi):
        out = []
        for k in range(int(lo // 1) - 1, int(hi // 1) + 2):
            a, b = max(lo, k + s0), min(hi, k + e0)
            if a < b:
                out.append((a, b))
        return out

    memo = {}

    def win(lo, hi, k):
        if (lo, hi, k) in memo:
            return memo[(lo, hi, k)]
        r = (X < lo and hi <= R0) or (k > 0 and any(
            all(win(*norm1(F(3, 2) * a + d, F(3, 2) * b + d), k - 1) for a, b in comps(lo, hi))
            for d in (F(0), H)))
        memo[(lo, hi, k)] = r
        return r

    def norm1(x, y):
        sh = x // 1
        return x - sh, y - sh

    return win(s0, e0, depth)


def verify(lo=BETA_EDGE, hi=BETA_SPLIT):
    """Open pieces with constant combinatorics, plus exact checks at the split points and at hi.
    Returns (everything won, #pieces, #points)."""
    todo, pieces, points, ok = [(lo, hi)], 0, {hi}, True
    while todo:
        a, b = todo.pop()
        try:
            ok = funnel(a, b) and ok
            pieces += 1
        except Split as sp:
            assert a < sp.at < b, (a, sp.at, b)
            points.add(sp.at)
            todo += [(a, sp.at), (sp.at, b)]
    ok = all(point_funnel(x) for x in points) and ok
    return ok, pieces, len(points)


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "verify":
        ok, n, m = verify()
        print(f"(a) adaptive funnel on beta in (7/57, 0.1229], depth {FUNNEL_DEPTH}: {ok}  "
              f"({n} open beta-pieces, {m} exact split points)")
        return 0 if ok else 1
    print(__doc__)
    return 2


# ---- persistent suite ----

def test_barrier_verifies():
    ok, _, _ = verify()
    assert ok


def test_funnel_fails_below_edge():
    # teeth: below 7/57 the constructor survives (relaxed certificates exist), so no funnel may exist
    ok, _, _ = verify(BETA_EDGE - F(1, 10 ** 4), BETA_EDGE - F(1, 10 ** 5))
    assert not ok


def test_hand_runaway_block():
    # the runaway lemma at a sample point, worked by hand: beta = 1/8, x = 0.55
    # R0 = 1 - 9/32 = 23/32; block (0,1/2,1/2) should give [27x/8 - 5/4, R0] = [0.60625, 0.71875]
    lo = F(1, 8) - F(1, 10 ** 9)
    st = [(Aff(F(55, 100)), Aff(1) - BETA.scale(F(9, 4)))]
    for d in (F(0), H, H):
        st = [c for w in st for c in children(w, d, lo, F(1, 8))]
    assert len(st) == 1
    wl, wh = st[0]
    assert wl.at(F(1, 8)) == F(27, 8) * F(55, 100) - F(5, 4) and wh.at(F(1, 8)) == F(23, 32)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
