#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Do integer parts behave like random 2-adic integers?  (StrongMahlerConjecture evidence, exact.)

D(m) = the largest N such that some xi in [m, m+1] keeps {xi (3/2)^n} in the arc [s, s+t] for n <= N
(nested exact intervals; each step multiplies by 3/2 and cuts by the arc's lifts).

Random model: N digits fix m mod 2^N and the arc admits ~lam^N digit words (arc_entropy.py), so a
"random" integer survives N steps with probability ~(lam/2)^N.  `rate` fits the survivor decay
S(N) = #{m < 2^K : D(m) >= N} between two depths and prints 2*rate, to compare with lam.

    arc_survival.py depth S T M CAP          D(m) for one integer part
    arc_survival.py rate S T K CAP LO HI     survivor decay over m < 2^K, depths LO..HI
    arc_survival.py test
"""
from __future__ import annotations

import math
import subprocess
import sys
from fractions import Fraction as F


def lifts(lo, hi, s, t):
    """Pieces of [lo, hi] inside the lifts [k + s, k + s + t]."""
    out = []
    for k in range(math.floor(lo - s) - 1, math.floor(hi - s) + 2):
        a, b = max(lo, k + s), min(hi, k + s + t)
        if a <= b:
            out.append((a, b))
    return out


def depth(m, s, t, cap):
    pieces, n = lifts(F(m), F(m + 1), s, t), -1
    while pieces and n < cap:
        n += 1
        if n == cap:
            break
        pieces = [q for a, b in pieces for q in lifts(F(3, 2) * a, F(3, 2) * b, s, t)]
    return n


def survivors(s, t, K, cap):
    return [depth(m, s, t, cap) for m in range(1, 2 ** K)]


def rate(D, lo, hi):
    S = lambda N: sum(d >= N for d in D)
    return S(lo), S(hi), (S(hi) / S(lo)) ** (1 / (hi - lo))


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "depth":
        s, t, m, cap = F(argv[1]), F(argv[2]), int(argv[3]), int(argv[4])
        print(f"m={m} arc [{s}, {s + t}]: depth {depth(m, s, t, cap)} (cap {cap})")
        return 0
    if argv[0] == "rate":
        s, t, K, cap, lo, hi = F(argv[1]), F(argv[2]), int(argv[3]), int(argv[4]), int(argv[5]), int(argv[6])
        D = survivors(s, t, K, cap)
        a, b, r = rate(D, lo, hi)
        print(f"arc [{s}, {s + t}] m < 2^{K}: S({lo})={a} S({hi})={b} 2*rate={2 * r:.4f} max depth {max(D)}")
        return 0
    print(__doc__)
    return 2


# ---- persistent suite ----

def _cli(*args):
    return subprocess.run([sys.executable, __file__, *args], capture_output=True, text=True)


def test_closed_afs_arc_never_dies():
    # relaxedStrategy_afs_closed: every integer part keeps a xi in {||x|| <= 1/3} forever
    assert all(d == 40 for d in survivors(F(2, 3), F(2, 3), 7, 40))


def test_mahler_arc_decays_at_flattos_rate():
    # Flatto 1992 Thm 6.1: Z-numbers up to x number O(x^{log2(3/2)}), i.e. lam = 3/2 on [0, 1/2]
    r = _cli("rate", "0", "1/2", "12", "80", "8", "20")
    two_rate = float(r.stdout.split("2*rate=")[1].split()[0])
    assert 1.4 <= two_rate <= 1.6, r.stdout


def test_short_arc_dies_everywhere():
    # teeth: FLP, every orbit's range is >= 1/3, so an arc of length 3/10 holds no integer part forever
    assert max(survivors(F(0), F(3, 10), 8, 200)) < 200


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
