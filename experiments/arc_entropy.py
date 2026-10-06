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
    arc_entropy.py backward T SAMPLES   sampled full depth of backward point trees vs card_backward_le
    arc_entropy.py afs EPS              check the explicit strategy holding {||x|| <= 1/3 + EPS}
    arc_entropy.py edge S M             where growth reaches 2 at position S, vs the game's edge
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


def matrix(s, t, m, inner=False):
    """Integer transfer matrix on the interval states reachable from the arc pieces.  Outward rounding
    (default) overcounts words, so its growth is an upper bound.  inner=True rounds inward and keeps
    one piece per digit: every counted word is genuinely admissible, so its growth is a lower bound."""
    A = pieces(s, t)

    def step(S):
        out = []
        for a in DIG:
            L, H = F(3, 2) * S[0] - a, F(3, 2) * S[1] - a
            for p0, p1 in A:
                lo, hi = max(L, p0), min(H, p1)
                if inner:
                    lo, hi = F(math.ceil(lo * m), m), F(math.floor(hi * m), m)
                    if lo < hi:
                        out.append((lo, hi))
                        break
                elif lo <= hi:
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


def growth(s, t, m, inner=False):
    """Float spectral radius (the number certify() tries to beat)."""
    return float(max(abs(np.linalg.eigvals(np.array(matrix(F(s), F(t), m, inner), dtype=float)))))


def entropy_edge(s, m, lo=F(1, 3), hi=F(1), steps=14):
    """Bracket the arc length where the true digit-word growth at position s reaches 2:
    (length where the upper bound reaches 2, length where the lower bound reaches 2)."""
    out = []
    for inner in (False, True):
        a, b = lo, hi
        for _ in range(steps):
            mid = (a + b) / 2
            if growth(s, mid, m, inner) >= 2:
                b = mid
            else:
                a = mid
        out.append(b)
    return tuple(out)


def game_edge(s, widths=12, lo=F(1, 3), hi=F(1), steps=12):
    """Shortest arc length at position s that a memoryless relaxed strategy holds, with the constructor
    free to use any of `widths` window widths (bisection; returns the smallest winning length)."""
    from arc_trap_k import solve_vw
    a, b = lo, hi
    for _ in range(steps):
        mid = (a + b) / 2
        L = [mid * F(3, 2) * F(j, widths) for j in range(1, widths)]
        P, fx = solve_vw(0, F(s), mid, L, iters=3000)
        if fx and any(x for row in P for x in row):
            b = mid
        else:
            a = mid
    return b


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


# ---- the hand proof below 2/3: point trees (exact, in actual fractional parts) ----

def in_arc(x, s, t):
    return (x - s) % 1 <= t


def predecessors(q, s, t):
    """x in [0, 1) in the arc with 3x/2 - a/2 = q for an integer a: x in 2q/3 + Z/3."""
    x0 = (F(2, 3) * q) % F(1, 3)
    return [x for x in (x0, x0 + F(1, 3), x0 + F(2, 3)) if in_arc(x, s, t)]


def successors(p, s, t):
    y0 = (F(3, 2) * p) % F(1, 2)
    return [y for y in (y0, y0 + F(1, 2)) if in_arc(y, s, t)]


def tree_count(x, s, t, n, step):
    level = [x]
    for _ in range(n):
        level = [y for z in level for y in step(z, s, t)]
    return len(level)


def word_count(s, t, N):
    """Exact number of digit words of length N with a nondegenerate cylinder (non-wrapping arc)."""
    cur = [(s, s + t)]
    for _ in range(N):
        nxt = []
        for lo, hi in cur:
            for a in DIG:
                l2, h2 = max(F(3, 2) * lo - a, s), min(F(3, 2) * hi - a, s + t)
                if l2 < h2:
                    nxt.append((l2, h2))
        cur = nxt
    return len(cur)


def lemma_depth(t):
    """card_backward_le: the first j with (2/3)^j < 2 - 3t; no backward tree is full past depth j."""
    return next(j for j in range(10 ** 4) if F(2, 3) ** j < 2 - 3 * t)


def full_depth(q, s, t, cap):
    """Depth to which the backward tree into q stays full binary (cap if it never breaks)."""
    level = [q]
    for d in range(cap):
        nxt = []
        for z in level:
            pre = predecessors(z, s, t)
            if len(pre) < 2:
                return d
            nxt += pre
        level = nxt
    return cap


# ---- the AFS half: an explicit strategy for {||x|| <= 1/3 + e}, every e > 0 ----

def afs_set(e):
    """P = [1/2 - 3e/2, 2/3) u [5/6 - 3e/2, 1), half-open (relaxedStrategy_afs)."""
    return [(F(1, 2) - F(3, 2) * e, F(2, 3)), (F(5, 6) - F(3, 2) * e, ONE)]


def in_set(x, P):
    return any(lo <= x < hi for lo, hi in P)


def afs_move(a, d, e):
    """The hand proof's witness u for window start a and parity d."""
    if a < F(2, 3):                                   # first piece
        return max(a, F(2, 3) - e)
    if d == 0:                                        # second piece
        return max(a, 1 - e)
    return max(a, F(8, 9) - e)


def relaxed_move_ok(a, d, u, s, t, l, P):
    """RelaxedStrategy's conditions, exactly as in ArcTrap.lean."""
    w = 2 * l / 3
    lift = any(k + s <= u and u + w <= k + s + t for k in range(-1, 3))
    c = F(3, 2) * u + d
    return a <= u and u + w <= a + l and lift and in_set(c - math.floor(c), P)


def afs_check(e, n=600):
    """Every a on a fine grid of P plus all endpoints, both parities: the witness works."""
    s, t, l, P = F(2, 3) - e, F(2, 3) + 2 * e, F(1, 2) + F(3, 2) * e, afs_set(e)
    pts = [lo + (hi - lo) * F(i, n) for lo, hi in P for i in range(n)]
    pts += [hi - F(1, 10 ** 12) for _, hi in P]
    return all(relaxed_move_ok(a, d, afs_move(a, d, e), s, t, l, P) for a in pts for d in (0, F(1, 2)))


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "bound":
        s, t, m = F(argv[1]), F(argv[2]), int(argv[3])
        b = bound(s, t, m)
        print(f"arc [{s}, {s + t}] grid 1/{m}: growth {growth(s, t, m):.4f}; certified < 2: "
              + (f"yes, W_N = O({b}^N)" if b else "no"))
        return 0
    if argv[0] == "edge":
        # arc_entropy.py edge S M : entropy-edge bracket vs game edge at position S
        sp, m = F(argv[1]), int(argv[2])
        e_up, e_lo = entropy_edge(sp, m)
        g = game_edge(sp)
        print(f"s={float(sp):.4f}  growth reaches 2 at length in [{float(e_up):.4f}, {float(e_lo):.4f}]"
              f"   game holds from {float(g):.4f}", flush=True)
        return 0
    if argv[0] == "backward":
        # arc_entropy.py backward T SAMPLES : worst full depth of backward trees vs the lemma
        import random
        t, n = F(argv[1]), int(argv[2])
        random.seed(0)
        worst = max(full_depth(F(random.randrange(10 ** 6), 10 ** 6), F(random.randrange(10 ** 6), 10 ** 6),
                               t, lemma_depth(t) + 3) for _ in range(n))
        print(f"length {t}: backward trees full to depth <= {worst} over {n} samples; lemma bound {lemma_depth(t)}")
        return 0 if worst <= lemma_depth(t) else 1
    if argv[0] == "afs":
        # arc_entropy.py afs EPS : check the explicit strategy for {||x|| <= 1/3 + EPS}
        e = F(argv[1])
        ok = afs_check(e)
        print(f"eps={e}: explicit AFS strategy " + ("holds" if ok else "FAILS"))
        return 0 if ok else 1
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


def test_two_thirds_is_critical():
    # hand (two_pow_le_card_admissibleWord): at non-wrapping length 2/3 Lebesgue is an eigenmeasure with
    # eigenvalue 4/3 and cylinders are <= (2/3)^N long, so W_N >= 2^N: the upper bound must reach 2 and
    # the certifier must refuse; just below, at 13/20, it must accept
    assert growth(0, F(2, 3), 160) >= 2 - 1e-9
    assert growth(F(1, 6), F(2, 3), 160) >= 2 - 1e-9
    assert bound(0, F(2, 3), 160) is None
    assert bound(F(1, 6), F(13, 20), 160) is not None


def test_lower_bound_below_upper():
    # inner rounding undercounts, outer overcounts; on Mahler's arc both must straddle Flatto's 3/2
    assert growth(0, F(1, 2), 160, inner=True) <= 1.5 + 1e-9 <= growth(0, F(1, 2), 160) + 2e-9


def test_game_reaches_afs_arc():
    # the arc {||x|| <= 1/3 + e} (Akiyama-Frougny-Sakarovitch's 1/3, set by hand) is held from every integer
    # part; removing e from either end loses
    from arc_trap_k import solve_vw, vw_orbit, dist_int
    e = F(1, 10 ** 6)

    def win(s, t):
        L = [t * F(3, 4)]
        P, fx = solve_vw(0, s, t, L, iters=4000)
        return (P, L) if fx and any(x for row in P for x in row) else None

    got = win(F(2, 3) - e, F(2, 3) + 2 * e)
    assert got
    P, L = got
    for m0 in (1, 2, 100):
        xi = vw_orbit(P, 0, F(2, 3) - e, F(2, 3) + 2 * e, L, m0, 50)
        assert m0 <= xi < m0 + 3
        assert max(dist_int(xi * F(3, 2) ** n) for n in range(50)) <= F(1, 3) + e
    assert not win(F(2, 3), F(2, 3) + e)
    assert not win(F(2, 3) - e, F(2, 3) + e)


def test_lemma_depth_by_hand():
    # (2/3)^1 = 0.667 >= 1/2 > (2/3)^2; (2/3)^7 = 0.0585 >= 0.05 > (2/3)^8 = 0.039
    assert lemma_depth(F(1, 2)) == 2 and lemma_depth(F(13, 20)) == 8


def test_backward_trees_break_by_the_lemma_depth():
    for t in ("1/2", "3/5", "13/20", "33/50"):
        r = _cli("backward", t, "150")
        assert r.returncode == 0, r.stdout


def test_backward_lemma_has_teeth():
    # at exactly 2/3 every point has two predecessors (hand: 3I/2 has length 1), so trees never break
    assert full_depth(F(1, 7), F(0), F(2, 3), 12) == 12
    assert full_depth(F(2, 7), F(1, 5), F(2, 3), 12) == 12


def test_forward_counts_are_fibonacci_bounded():
    # card_forward_le: below 3/4 sibling successors never both branch, so counts <= fib(N + 2)
    fib = [0, 1]
    for _ in range(20):
        fib.append(fib[-1] + fib[-2])
    import random
    random.seed(3)
    for _ in range(200):
        s, p = F(random.randrange(1000), 1000), F(random.randrange(1000), 1000)
        for N in (3, 8):
            assert tree_count(p, s, F(37, 50), N, successors) <= fib[N + 2]
    # teeth: at length 0.8 the four quarter points fit, so two steps reach 4 > fib(4) = 3
    assert any(tree_count(F(i, 400), F(0), F(4, 5), 2, successors) == 4 for i in range(400))


def test_backward_count_matches_lemma_bound():
    # card_backward_le at t = 33/50: K = lemma_depth + 1 = 11 steps leave at most 2^11 - 1 paths
    import random
    random.seed(5)
    t = F(33, 50)
    K = lemma_depth(t) + 1
    for _ in range(40):
        q, s = F(random.randrange(1000), 1000), F(random.randrange(1000), 1000)
        assert tree_count(q, s, t, K, predecessors) <= 2 ** K - 1


def test_decomposition_bounds_the_words():
    # admissibleWord_growth_lt_two, first step: a word splits at its left-edge hit into a backward path
    # into s (length j) and a forward path (<= fib(N - j + 2)); the sum must dominate the exact count
    fib = [0, 1]
    for _ in range(30):
        fib.append(fib[-1] + fib[-2])
    for s0, t in ((F(1, 10), F(33, 50)), (F(1, 5), F(3, 5)), (F(0), F(1, 2))):
        for N in (6, 10):
            bound = sum(tree_count(s0, s0, t, j, predecessors) * fib[N - j + 2] for j in range(N + 1))
            assert word_count(s0, t, N) <= bound


def test_afs_strategy_every_eps():
    # relaxedStrategy_afs: the hand proof's witnesses satisfy RelaxedStrategy exactly
    for e in ("1/10", "1/100", "1/1000000", "1/10000000000"):
        r = _cli("afs", e)
        assert r.returncode == 0 and "holds" in r.stdout, r.stdout


def test_afs_strategy_needs_positive_eps():
    # hand: at e = 0 the d = 0 move from the first piece needs u in [2/3, 2/3), which is empty
    assert not afs_check(F(0))
    assert not relaxed_move_ok(F(3, 5), 0, F(2, 3), F(2, 3), F(2, 3), F(1, 2), afs_set(F(0)))


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
