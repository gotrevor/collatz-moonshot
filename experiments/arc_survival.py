#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Do integer parts behave like random 2-adic integers?  (StrongMahlerConjecture evidence, exact.)

D(m) = the largest N such that some xi in [m, m+1] keeps {xi (3/2)^n} in the arc [s, s+t] for n <= N
(nested exact intervals; each step multiplies by 3/2 and cuts by the arc's lifts).

Random model: N digits fix m mod 2^N and the arc admits ~lam^N digit words (arc_entropy.py), so a
"random" integer survives N steps with probability ~(lam/2)^N.  `rate` fits the survivor decay
S(N) = #{m < 2^K : D(m) >= N} between two depths and prints 2*rate, to compare with lam.

    arc_survival.py depth S T M CAP          D(m) for one integer part
    arc_survival.py rate S T K CAP LO HI     survivor decay over m < 2^K, depths LO..HI
    arc_survival.py profile S T K CAP        S(N) at N = CAP/8, CAP/4, CAP/2, CAP (plateau vs decay)
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


def run_bounded_count(R, N):
    """Binary words of length N with no run of equal letters longer than R (DP on the current run)."""
    if N == 0:
        return 1
    row = {1: 2}
    for _ in range(N - 1):
        nxt = {}
        for r, c in row.items():
            if r + 1 <= R:
                nxt[r + 1] = nxt.get(r + 1, 0) + c
            nxt[1] = nxt.get(1, 0) + c
        row = nxt
    return sum(row.values())


def afs_error_orbit(delta, g, N, grow=F(3, 2)):
    """Follow the piece g + [0, 1/3 + delta] with the endpoint-error recursion of near_afs_density.
    Returns ("ok", N), ("cond", n) when the recursion's conditions fail first, or ("MISMATCH", n)."""
    s, t = F(2, 3) + delta, F(2, 3)
    k, side, eL, eR = g, 0, F(0), delta
    for n in range(N):
        a = k + (eL if side == 0 else F(2, 3) + eL)
        b = k + (F(1, 3) if side == 0 else 1) + eR
        par = k % 2
        L, Rr = F(3, 2) * eL - delta, F(3, 2) * eR - delta
        ok = (-F(1, 3) <= L <= F(1, 3) and -F(1, 6) <= Rr < F(1, 6)) if par == 0 else \
             (-F(1, 6) < L <= F(1, 6) and -F(1, 3) <= Rr <= F(1, 3))
        if not ok:
            return "cond", n
        img = lifts(F(3, 2) * a, F(3, 2) * b, s, t)
        base = F(3, 2) * k + side
        if par == 0:
            eL, eR, side, k = grow * eL, delta, 0, base
        else:
            eL, eR, side, k = delta, grow * eR, 1, base - F(1, 2)
        k = int(k)
        want = (k + (eL if side == 0 else F(2, 3) + eL), k + (F(1, 3) if side == 0 else 1) + eR)
        if img != [want]:
            return "MISMATCH", n
    return "ok", N


def afs_unbroken(delta, w):
    """Word-level recursion of near_afs_density: errors (eL, eR) start (0, delta); letter 0 maps them
    to (3eL/2, delta), letter 1 to (delta, 3eR/2); each step must pass AfsStepOk."""
    eL, eR = F(0), delta
    for b in w:
        L, Rr = F(3, 2) * eL - delta, F(3, 2) * eR - delta
        ok = (-F(1, 6) < L <= F(1, 6) and -F(1, 3) <= Rr <= F(1, 3)) if b else \
             (-F(1, 3) <= L <= F(1, 3) and -F(1, 6) <= Rr < F(1, 6))
        if not ok:
            return False
        eL, eR = (delta, F(3, 2) * eR) if b else (F(3, 2) * eL, delta)
    return True


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
    if argv[0] == "profile":
        s, t, K, cap = F(argv[1]), F(argv[2]), int(argv[3]), int(argv[4])
        D = survivors(s, t, K, cap)
        pts = [cap // 8, cap // 4, cap // 2, cap]
        print(f"s={s} t={t} m < 2^{K}: " + " ".join(f"S({n})={sum(d >= n for d in D)}" for n in pts), flush=True)
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



def _profile(sp, K, cap):
    r = _cli("profile", sp, "2/3", str(K), str(cap))
    return [int(w.split("=")[1]) for w in r.stdout.split() if w.startswith("S(")]


def test_length_two_thirds_plateaus_only_at_afs():
    # AfsArcIsUniqueMinimal evidence.  Hand: at s = 2/3 every integer part survives (closed strategy);
    # the random model at lam = 2 is a critical branching process, so elsewhere S(N) must keep falling
    assert _profile("2/3", 7, 160) == [127] * 4
    S = _profile("0", 7, 160)
    assert S[0] > S[1] > S[2] > S[3] and S[3] < S[0] / 2



def test_endpoint_error_recursion_is_exact():
    # near_afs_density's recursion, checked against exact lift cuts while its conditions hold
    for delta in (F(1, 30), F(-1, 30), F(1, 200), F(-3, 500)):
        for g in range(1, 200):
            assert afs_error_orbit(delta, g, 25)[0] in ("ok", "cond")
    # teeth: a wrong growth factor is caught
    assert any(afs_error_orbit(F(1, 30), g, 25, grow=F(2))[0] == "MISMATCH" for g in range(1, 50))


def test_run_bounded_count_bound():
    # hand: length 4, runs <= 2: 16 minus 0000 0001 1000 1111 1110 0111 = 10; runs <= 1: only 0101, 1010
    assert run_bounded_count(2, 4) == 10 and run_bounded_count(1, 7) == 2
    # run_bounded_count_ge
    for R in range(1, 12):
        for N in range(1, 200):
            assert run_bounded_count(R, N) >= 2 ** N * (1 - F(1, 2 ** R)) ** N


def test_near_afs_density_small_case():
    # near_afs_density at delta = 1/30: (3/2)^3/30 + 1/30 < 1/6 allows R = 2
    d, N = F(1, 30), 8
    trapped = sum(depth(g, F(2, 3) + d, F(2, 3), N) >= N for g in range(2 ** N))
    assert run_bounded_count(2, N) <= trapped



def test_afs_event_rate_bounds():
    # near_afs_event_rate at delta = 1/30.  Hand: R = 2 since (3/2)^3/30 + 1/30 < 1/6 <= (3/2)^4/30 + 1/30;
    # m = 6 since (1/30)((3/2)^6 - 1) = 0.346 > 1/3 >= (1/30)((3/2)^5 - 1) = 0.220.
    from itertools import product
    d, R, m = F(1, 30), 2, 6
    for N in (8, 12, 14):
        unbroken = sum(afs_unbroken(d, w) for w in product((0, 1), repeat=N))
        assert run_bounded_count(R, N) <= unbroken <= 2 ** N * (1 - F(1, 2 ** m)) ** (N // (m + 1))
    # the forcing pattern really breaks: a flip then six equal letters
    assert not afs_unbroken(d, (1, 0, 0, 0, 0, 0, 0)) and afs_unbroken(d, (1, 0, 0, 0, 0, 0))


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
