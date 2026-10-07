#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Oblivious kills: choose the binary digits of m in advance so that every xi in [m, m + 3) has
||xi (3/2)^n|| < beta for some n.  One such m defeats every finite-memory strategy at once
(ObliviousKill / not_kRelaxedStrategy_of_obliviousKill in ArcTrap.lean).

State after t digits: the exact intervals of V = xi (3/2)^t for xi in [m_t, m_t + 3), m_t = m mod 2^t.
Digit t adds 3^t to V (an integer now, a half-integer parity flip after the next x 3/2).  Beam search
keeps the `width` digit prefixes with the smallest score sum(len_y ** exp), len_y the component length
pulled back to xi.

Found 2026-10-07: kills at 3/20 (depth 20), 29/200 (25), 7/50 (36), 69/500 (51,
m = 356318813878270), 0.1379 (53), 0.1378 (62), 0.1377 (66, m = 31982856860489480190, exp 1.0), each
re-checked by arc_fullinfo.survives; none at 0.137, 0.1365, 0.136 with width 20000.

    arc_oblivious.py search BETA DEPTH WIDTH [EXP]
    arc_oblivious.py test
"""
from __future__ import annotations

import subprocess
import sys
from fractions import Fraction as F

def search(beta, depth, width, exp=0.5, start=3, log=False):
    """(kill depth, m) for the first kill the beam finds, else (None, None).

    Integer arithmetic: with beta = p/q, endpoints of V are numerators over q * 2^t, so x 3/2 is a
    numerator x 3 and the digit-t shift 3^t is 3^t * q * 2^t."""
    beta = F(beta)
    p, q = beta.numerator, beta.denominator
    beam = [(0, [(0, start * q)])]
    for t in range(depth):
        den = q << t
        sh = 3 ** t * den
        lo_off, hi_off = p << t, (q - p) << t
        nd = (q << (t + 1)) * 1.5 ** (t + 1)
        cand = []
        for m, ivs in beam:
            for d in (0, 1):
                nxt = []
                for lo, hi in ivs:
                    if d:
                        lo, hi = lo + sh, hi + sh
                    for j in range(lo // den - 1, hi // den + 1):
                        a, c = max(lo, j * den + lo_off), min(hi, j * den + hi_off)
                        if a <= c:
                            nxt.append((3 * a, 3 * c))
                m2 = m | (d << t)
                if not nxt:
                    return t + 1, m2
                score = sum(((c - a) / nd) ** exp for a, c in nxt)
                cand.append((score, len(nxt), m2, nxt))
        cand.sort(key=lambda c: (c[0], c[1]))
        beam = [(c[2], c[3]) for c in cand[:width]]
        if log and t % 10 == 9:
            print(f"  t={t + 1} best score {cand[0][0]:.3e} comps {cand[0][1]}", flush=True)
    return None, None


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "search":
        exp = float(argv[4]) if len(argv) > 4 else 0.5
        print(search(F(argv[1]), int(argv[2]), int(argv[3]), exp, log=True))
        return 0
    print(__doc__)
    return 2


# ---- persistent suite ----

def _dies_exactly_at(m, beta, n):
    from arc_fullinfo import survives
    return not survives(F(m), F(m + 3), beta, n) and survives(F(m), F(m + 3), beta, n - 1)


def test_kill_at_three_twentieths_checked_independently():
    t, m = search(F(3, 20), 30, 300)
    assert t is not None and _dies_exactly_at(m, F(3, 20), t)


def test_recorded_kill_138():
    # obliviousKill_138: the independent interval tree, not the search, is the judge
    assert _dies_exactly_at(356318813878270, F(69, 500), 51)
    # only m mod 2^51 matters for 51 steps
    assert _dies_exactly_at(356318813878270 + 2 ** 51, F(69, 500), 51)


def test_recorded_kill_1377():
    # obliviousKill_1377, the lowest kill found (2026-10-07)
    assert _dies_exactly_at(31982856860489480190, F(1377, 10000), 66)


def test_no_kill_below_seven_57():
    # control: relaxedStrategy_757 traps every class at 7/57, so no oblivious kill exists below it
    assert search(F(12, 100), 30, 200) == (None, None)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
