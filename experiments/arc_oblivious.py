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

    arc_oblivious.py search BETA DEPTH WIDTH [EXP [START_WIDTH [OFFSET]]]
    arc_oblivious.py relaxed BETA L DEPTH WIDTH [EXP [L2]]   (L2: every width in [L, L2])
    arc_oblivious.py test
"""
from __future__ import annotations

import subprocess
import sys
from fractions import Fraction as F

def search(beta, depth, width, exp=0.5, start=3, log=False, offset=0):
    """(kill depth, m) for the first kill the beam finds, else (None, None).

    The start set is [m + offset, m + offset + start).

    Integer arithmetic: with beta = p/q, endpoints of V are numerators over q * 2^t, so x 3/2 is a
    numerator x 3 and the digit-t shift 3^t is 3^t * q * 2^t."""
    beta, start, offset = F(beta), F(start), F(offset)
    q = beta.denominator * start.denominator * offset.denominator
    p = int(beta * q)
    beam = [(0, [(int(offset * q), int((offset + start) * q))])]
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


def search_relaxed(beta, l, depth, width, exp=1.0, log=False, l2=None):
    """Relaxed oblivious kill (RelaxedObliviousKill): reachable LEFT ENDS V of width-l windows, in actual
    numbers.  Move u in [V, V + l/3] with [u, u + 2l/3] in a lift of [beta, 1 - beta]; next 3u/2.
    Start: [m, m + 1).  Numerators over Q * 2^t with Q = 3 * den(beta) * den(l) * den(l2).
    With l2: every width in [l, l2] at once (RelaxedObliviousKillRange): spread l2/3, margin 2l/3."""
    beta, l = F(beta), F(l)
    l2 = l if l2 is None else F(l2)
    Q = beta.denominator * l.denominator * l2.denominator * 3
    P, L3, S3 = int(beta * Q), int(l * Q) // 3, int(l2 * Q) // 3
    beam = [(0, [(0, Q)])]
    for t in range(depth):
        den = Q << t
        sh = 3 ** t * den
        lo_off, hi_off, spread = P << t, (Q - P - 2 * L3) << t, S3 << t
        nd = float(den) * 2 * 1.5 ** (t + 1)
        cand = []
        for m, ivs in beam:
            for d in (0, 1):
                nxt = []
                for lo, hi in ivs:
                    if d:
                        lo, hi = lo + sh, hi + sh
                    hi2 = hi + spread
                    for j in range(lo // den - 1, hi2 // den + 1):
                        a, c = max(lo, j * den + lo_off), min(hi2, j * den + hi_off)
                        if a <= c:
                            nxt.append((3 * a, 3 * c))
                nxt.sort()
                mg = []
                for a, c in nxt:
                    if mg and a <= mg[-1][1]:
                        mg[-1] = (mg[-1][0], max(mg[-1][1], c))
                    else:
                        mg.append((a, c))
                m2 = m | (d << t)
                if not mg:
                    return t + 1, m2
                score = sum(((c - a) / nd + float(l2) / 1.5 ** (t + 1)) ** exp for a, c in mg)
                cand.append((score, len(mg), m2, mg))
        cand.sort(key=lambda c: (c[0], c[1]))
        beam = [(c[2], c[3]) for c in cand[:width]]
        if log and t % 10 == 9:
            print(f"  t={t + 1} best score {cand[0][0]:.3e} comps {cand[0][1]}", flush=True)
    return None, None


def relaxed_check(beta, l, m, depth, l2=None):
    """Independent judge in KRelaxedStrategy's own bookkeeping: state (r mod 2^K, fractional left end),
    child fract(3u/2 + d), residue ((3r - r%2)/2 + floor) mod 2^(K-1), K > depth.  First dead depth or None."""
    import math
    beta, l = F(beta), F(l)
    l2 = l if l2 is None else F(l2)
    K = depth + 2
    st = {m % (1 << K): [(F(0), F(1))]}
    for t in range(1, depth + 1):
        new = {}
        for r, ivs in st.items():
            d = F(r % 2, 2)
            for A, B in ivs:
                for j in (0, 1, 2):
                    a, c = max(A, j + beta), min(B + l2 / 3, j + 1 - beta - 2 * l / 3)
                    if a > c:
                        continue
                    lo, hi = F(3, 2) * a + d, F(3, 2) * c + d
                    for fl in range(math.floor(lo), math.floor(hi) + 1):
                        x, y = max(lo, F(fl)), min(hi, F(fl + 1))
                        if x > y or x == fl + 1:
                            continue
                        r2 = ((3 * r - r % 2) // 2 + fl) % (1 << (K - 1))
                        new.setdefault(r2, []).append((x - fl, y - fl))
        st = new
        if not st:
            return t
    return None


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "relaxed":
        exp = float(argv[5]) if len(argv) > 5 else 1.0
        l2 = F(argv[6]) if len(argv) > 6 else None
        print(search_relaxed(F(argv[1]), F(argv[2]), int(argv[3]), int(argv[4]), exp, log=True, l2=l2))
        return 0
    if argv[0] == "search":
        exp = float(argv[4]) if len(argv) > 4 else 0.5
        start = F(argv[5]) if len(argv) > 5 else 3
        offset = F(argv[6]) if len(argv) > 6 else 0
        print(search(F(argv[1]), int(argv[2]), int(argv[3]), exp, start=start, log=True, offset=offset))
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


def test_relaxed_kill_1_8_checked_independently():
    # relaxedObliviousKill_1_8: the beam finds m, the residue-bookkeeping judge confirms the depth
    t, m = search_relaxed(F(1, 8), F(1, 8), 40, 2000)
    assert (t, m) == (22, 604160)
    assert relaxed_check(F(1, 8), F(1, 8), 604160, 30) == 22
    assert relaxed_check(F(1, 8), F(1, 8), 604161, 30) is None


def test_relaxed_no_kill_below_seven_57():
    # control: relaxedStrategy_757 (l = 1/8) survives every start below 7/57
    assert relaxed_check(F(12, 100), F(1, 8), 604160, 30) is None
    assert search_relaxed(F(12, 100), F(1, 8), 30, 300) == (None, None)


def test_certificates_013():
    # finiteMemoryRelaxedValue_ge_013's three certificates, judged by the independent checkers
    from arc_fullinfo import survives
    m, b = 13060715579013119, F(13, 100)
    assert not survives(F(m), F(m) + F(3, 2), b, 56) and survives(F(m), F(m) + F(3, 2), b, 55)
    assert relaxed_check(b, F(1, 2), 1048576, 20, l2=F(3, 4)) == 5
    assert relaxed_check(b, F(3, 4), 1048584, 20, l2=F(111, 100)) == 7


def test_start_width_matters():
    # from [m, m + 1) component kills reach 0.13; the same beam from [m, m + 3) does not by depth 45
    t, m = search(F(13, 100), 45, 1000, 1.0, start=1)
    assert t == 38
    assert search(F(13, 100), 45, 1000, 1.0, start=3) == (None, None)


TILES_1229 = [(568234, 21), (58965761, 27), (1077873, 22), (17399807417632, 47), (1019278, 22),
              (8143102, 27), (480341, 21), (3, 4)]


def test_tiles_1229():
    # obliviousKillAt_1229_tiles: [m_i + i/8, m_i + i/8 + 1/4] dies within D_i at 0.1229, for i < 8;
    # closed intervals, judged by the independent interval tree
    from arc_fullinfo import survives
    b = F(1229, 10000)
    for i, (m, d) in enumerate(TILES_1229):
        lo = m + F(i, 8)
        assert not survives(lo, lo + F(1, 4), b, d) and survives(lo, lo + F(1, 4), b, d - 1)
    # control: the hardest tile does not die at 0.12285 by the same depth
    assert survives(TILES_1229[3][0] + F(3, 8), TILES_1229[3][0] + F(5, 8), F(12285, 100000), 47)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
