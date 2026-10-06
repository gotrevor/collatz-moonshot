#!/usr/bin/env -S uv run --quiet --with pytest --with numpy python3
"""Finite-memory barrier by counting (exact rationals): Flatto's entropy method on an arbitrary arc.

Z(I) = {xi > 0 : {xi (3/2)^n} in I for all n}.  Write g_n = floor(xi (3/2)^n), f_n = frac, and the
digit a_n = g_{n+1} - 3 g_n / 2 = 3 f_n / 2 - f_{n+1}, a half-integer in {-1/2, 0, 1/2, 1}.
  (1) 3^N g_0 = 2^N g_N - sum_n 3^(N-1-n) 2^(n+1) a_n, so a digit word of length N fixes g_0 mod 2^N.
  (2) Hence #{g in [0, 2^N) : g = floor(xi), xi in Z(I)} <= W_N(I), the number of digit words with
      f_0..f_N in I and f_{n+1} = 3 f_n / 2 - a_n.
  (3) A finite-memory strategy (any k) traps some xi in [m, m + 2) for EVERY m = r mod 2^k, so that
      count is >= 2^(N - k - 1) - 1.  If W_N <= C lam^N with lam < 2, no such strategy exists.
W_N is bounded by a transfer matrix: a state is an interval S of possible current f (outward-rounded to
the 1/m grid, so it only overcounts); S -> round(3S/2 - a) cut by each piece of I.  A rational vector
v > 0 with M v <= c v (Collatz-Wielandt) certifies W_N <= C c^N.

    arc_entropy.py bound S T M          growth bound for the arc [S, S+T] at grid 1/M
    arc_entropy.py cover T G M          certify every arc of length T (all positions, mesh 1/G)
    arc_entropy.py test
"""
from __future__ import annotations

import math
import subprocess
import sys
from fractions import Fraction as F

import numpy as np

DIG = (F(-1, 2), F(0), F(1, 2), F(1))
ONE = F(1)


def pieces(s, t):
    s = s % 1
    return [(s, s + t)] if s + t <= 1 else [(s, ONE), (F(0), s + t - 1)]


def matrix(s, t, m):
    """Integer transfer matrix on the outward-rounded interval states reachable from the arc pieces."""
    A = pieces(s, t)

    def step(S):
        out = []
        for a in DIG:
            L, H = F(3, 2) * S[0] - a, F(3, 2) * S[1] - a
            for p0, p1 in A:
                lo, hi = max(L, p0), min(H, p1)
                if lo <= hi:
                    out.append((max(F(math.floor(lo * m), m), p0), min(F(math.ceil(hi * m), m), p1)))
        return out

    idx = {p: i for i, p in enumerate(A)}
    todo, edges = list(A), []
    while todo:
        S = todo.pop()
        for T in step(S):
            if T not in idx:
                idx[T] = len(idx)
                todo.append(T)
            edges.append((idx[S], idx[T]))
    M = [[0] * len(idx) for _ in idx]
    for i, j in edges:
        M[i][j] += 1
    return M


def certify(M, c):
    """Exact check: a rational v > 0 with M v <= c v.  Returns True only on an exact success."""
    A = np.array(M, dtype=float)
    v = np.ones(len(M))
    for _ in range(3000):
        w = A @ v + 1e-9 * v.sum()
        v = w / w.max()
    q = [F(int(round(x * 10 ** 9)) + 1, 10 ** 9) for x in v]
    return all(sum(M[i][j] * q[j] for j in range(len(M)) if M[i][j]) <= c * q[i] for i in range(len(M)))


def growth(s, t, m):
    """Float spectral radius (the number certify() tries to beat)."""
    return float(max(abs(np.linalg.eigvals(np.array(matrix(F(s), F(t), m), dtype=float)))))


def bound(s, t, m, c=F(2)):
    """Smallest rational on a 1/1000 ladder below c that certify() accepts, or None."""
    M = matrix(F(s), F(t), m)
    rho = float(max(abs(np.linalg.eigvals(np.array(M, dtype=float)))))
    if rho >= c:
        return None
    for k in range(math.ceil(rho * 1000) + 1, math.ceil(c * 1000)):
        if certify(M, F(k, 1000)):
            return F(k, 1000)
    return None


def cover(t, G, m):
    """Every arc [s, s+t] lies in some [i/G, i/G + t + 1/G]; certify all G of those below 2."""
    worst = F(0)
    for i in range(G):
        b = bound(F(i, G), t + F(1, G), m)
        if b is None:
            return None, F(i, G)
        worst = max(worst, b)
    return worst, None


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "bound":
        s, t, m = F(argv[1]), F(argv[2]), int(argv[3])
        b = bound(s, t, m)
        print(f"arc [{s}, {s + t}] grid 1/{m}: growth {growth(s, t, m):.4f}; certified < 2: "
              + (f"yes, W_N = O({b}^N)" if b else "no"))
        return 0
    if argv[0] == "cover":
        t, G, m = F(argv[1]), int(argv[2]), int(argv[3])
        worst, fail = cover(t, G, m)
        if worst is None:
            print(f"length {t}: NOT certified (fails at position {fail})")
            return 1
        print(f"every arc of length {t}: digit words grow at most {worst}^N < 2^N "
              f"(mesh 1/{G}, grid 1/{m}) -> no finite-memory strategy")
        return 0
    print(__doc__)
    return 2


# ---- persistent suite ----

def _cli(*args):
    return subprocess.run([sys.executable, __file__, *args], capture_output=True, text=True)


def test_mahler_arc_between_flatto_and_golden_ratio():
    # hand: on [0, 1/2] two odd g in a row force f >= 5/9, so words avoid "11": growth <= golden ratio;
    # Flatto 1992's exponent log2(3/2) says the true growth is 3/2, which no upper bound can beat
    g = growth(0, F(1, 2), 80)
    assert 1.5 <= g <= (1 + 5 ** 0.5) / 2 + 1e-9
    r = _cli("bound", "0", "1/2", "40")
    assert r.returncode == 0 and "certified < 2: yes" in r.stdout


def test_cover_six_tenths():
    r = _cli("cover", "3/5", "400", "80")
    assert r.returncode == 0 and "no finite-memory strategy" in r.stdout


def test_game_witnesses_are_not_certified():
    # soundness teeth: arcs that a memoryless strategy provably holds (arc_trap_k.py) have positive
    # density of trapped integer parts, so their growth must be >= 2 and the certifier must refuse
    assert bound(F(4, 65), F(57, 65), 40) is None            # Pollington's arc (test_k0_matches_robust_game)
    assert bound(F(13, 20), F(7, 10), 40) is None             # shortest-arc witness region, length 0.7
    assert bound(F(307, 2500), 1 - 2 * F(307, 2500), 40) is None  # the 0.1228 certificate's arc


def test_certify_has_teeth():
    M = matrix(F(0), F(1, 2), 40)
    assert not certify(M, F(3, 2))   # below the true growth: must fail
    assert certify(M, F(17, 10))


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
