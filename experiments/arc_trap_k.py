#!/usr/bin/env -S uv run --quiet --with pytest python3
"""k-aware nested-interval game for {xi (3/2)^n} in an arc (exact rationals).

Extends arc_trap.py (the k = 0, parity-blind game).  The construction knows the integer part m of the
current window exactly, but a finite-state strategy can only remember m mod 2^k.  One step:
    y = 1.5 (m + a) = floor(3m/2) + (1.5 a + d),      d = (m mod 2)/2,
choose a child window [c, c + l] inside [y, y + 1.5 l]; its integer part is m' = floor(3m/2) + j with
j = floor(c - floor(3m/2)).  m' mod 2^(k-1) is determined by (m mod 2^k, j); the new top bit is not,
so the strategy must win for both lifts.  State set: for each r in Z/2^k a union of intervals P_r of
left ends a.  Greatest fixed point of
    P_r <- P_r ∩ { a : exists j, c in [1.5a + d_r, 1.5a + d_r + l/2], floor(c) = j,
                       frac(c) in P_{r'} ∩ P_{r' + 2^(k-1)},  r' = ((3r - r%2)/2 + j) mod 2^(k-1) }.
Nonempty fixed point => some xi > 0 has all fractional parts in the arc (start at any m ≡ r).
k = 0 (no memory, d adversarial) is arc_trap.robust_set.

    arc_trap_k.py check K S T L
    arc_trap_k.py certificate K BETA NL OUT.json          (window-in-arc game)
    arc_trap_k.py vw-certificate K BETA WLO WHI WDEN OUT  (relaxed game, widths WLO/WDEN..WHI/WDEN)
    arc_trap_k.py test

Relaxed game (solve_vw): only the sub-window the next step selects must lie in the arc.  Its value for
the symmetric arc [beta, 1 - beta] is 7/57 to 1e-8 for every k = 0..3 (conjecture; see the research note).
"""
from __future__ import annotations

import math
import subprocess
import sys
from fractions import Fraction as F

ONE, HALF = F(1), F(1, 2)


def norm(ivs):
    ivs = sorted((lo, hi) for lo, hi in ivs if lo < hi)
    out = []
    for lo, hi in ivs:
        if out and lo <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], hi))
        else:
            out.append((lo, hi))
    return out


def inter(A, B):
    out, i, j = [], 0, 0
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if lo < hi:
            out.append((lo, hi))
        if A[i][1] < B[j][1]:
            i += 1
        else:
            j += 1
    return out


def arc_left_ends(s, t, l):
    """Left ends a in [0,1) with [a, a+l] inside the arc [s, s+t] (mod 1), t < 1."""
    lo, hi = s, s + t - l
    if hi <= lo:
        return []
    k = lo // 1
    lo, hi = lo - k, hi - k
    if hi <= 1:
        return [(lo, hi)]
    return norm([(lo, ONE), (F(0), hi - 1)])


def step_targets(Pk, r, k, l):
    """Set of c-values (reals in [0, 3)) that are acceptable children from residue r."""
    out = []
    half = 1 << (k - 1) if k >= 1 else 0
    for j in range(3):
        if k == 0:
            T = Pk[0]
        else:
            r1 = ((3 * r - (r % 2)) // 2 + j) % half if half else 0
            T = inter(Pk[r1], Pk[r1 + half])
        out += [(lo + j, hi + j) for lo, hi in T]
    return norm(out)


def preimage(C, d, l):
    """{a in [0,1) : [1.5a + d, 1.5a + d + l/2] meets C}."""
    out = []
    for lo, hi in C:
        a0, a1 = (lo - l / 2 - d) / F(3, 2), (hi - d) / F(3, 2)
        a0, a1 = max(a0, F(0)), min(a1, ONE)
        if a0 < a1:
            out.append((a0, a1))
    return norm(out)


def solve(k, s, t, l, iters=500):
    base = arc_left_ends(s, t, l)
    n = 1 << k
    P = [list(base) for _ in range(n)]
    for _ in range(iters):
        new = []
        for r in range(n):
            if k == 0:
                acc = inter(preimage(step_targets(P, 0, 0, l), F(0), l),
                            preimage(step_targets(P, 0, 0, l), HALF, l))
            else:
                acc = preimage(step_targets(P, r, k, l), HALF if r % 2 else F(0), l)
            new.append(inter(P[r], acc))
        if new == P:
            return P, True
        P = new
        if all(not x for x in P):
            return P, True
    return P, False


# ---- relaxed, variable-width game ----
# The window W = m + [a, a + L[i]] need not sit in the arc.  A move picks a sub-window
# V = m + [u, u + 2 L[j]/3] of W that does sit in a lift of the arc; the child window is
# 1.5 V = floor(3m/2) + [c, c + L[j]], c = 1.5u + d.  Every y_n of the final xi lies in its V,
# so only V must be in the arc.  With L = [l] this dominates solve(): there W itself is in the arc.

def arc_u(s, t, w):
    """u with [u, u + w] inside some lift [k + s, k + s + t] of the arc."""
    return norm([(k + s, k + s + t - w) for k in range(-1, 5) if t > w])


def vw_targets(P, r, k, j):
    """c-values in [0, 5) whose child (width L[j]) is in the state set for every unseen lift."""
    half = 1 << (k - 1) if k >= 1 else 0
    out = []
    for J in range(5):
        if k == 0:
            T = P[0][j]
        else:
            r1 = ((3 * r - (r % 2)) // 2 + J) % half if half else 0
            T = inter(P[r1][j], P[r1 + half][j])
        out += [(lo + J, hi + J) for lo, hi in T]
    return norm(out)


def vw_good_u(P, r, k, j, d, s, t, L):
    w = 2 * L[j] / 3
    C = vw_targets(P, r, k, j)
    return inter(norm([((lo - d) / F(3, 2), (hi - d) / F(3, 2)) for lo, hi in C]), arc_u(s, t, w))


def vw_aset(P, r, k, i, j, d, s, t, L):
    """{a in [0,1) : some u in [a, a + L[i] - 2L[j]/3] is good}."""
    D = L[i] - 2 * L[j] / 3
    if D < 0:
        return []
    G = vw_good_u(P, r, k, j, d, s, t, L)
    return norm([(max(g0 - D, F(0)), min(g1, ONE)) for g0, g1 in G])


def round_in(ivs, N):
    """Shrink each interval to the 1/N grid (a subset, so post-fixed points stay certificates)."""
    out = []
    for lo, hi in ivs:
        lo2, hi2 = F(math.ceil(lo * N), N), F(math.floor(hi * N), N)
        if lo2 < hi2:
            out.append((lo2, hi2))
    return out


def solve_vw(k, s, t, L, iters=5000, N=1 << 24):
    """Greatest post-fixed point on the 1/N lattice: the sets only shrink and the lattice is finite, so
    this terminates; the result satisfies P <= step(P), which is all soundness needs."""
    n, q = 1 << k, len(L)
    P = [[[(F(0), ONE)] for _ in range(q)] for _ in range(n)]
    for _ in range(iters):
        new = []
        for r in range(n):
            row = []
            for i in range(q):
                if k == 0:
                    acc = inter(*[norm(sum((vw_aset(P, 0, 0, i, j, d, s, t, L) for j in range(q)), []))
                                  for d in (F(0), HALF)])
                else:
                    d = HALF if r % 2 else F(0)
                    acc = norm(sum((vw_aset(P, r, k, i, j, d, s, t, L) for j in range(q)), []))
                row.append(round_in(inter(P[r][i], acc), N))
            new.append(row)
        if new == P:
            return P, True
        P = new
        if all(not x for row in P for x in row):
            return P, True
    return P, False


def vw_orbit(P, k, s, t, L, m0, steps):
    """Independent check: play the certificate against the TRUE integer parts from m0 and return the
    exact xi (left end of the final window).  Raises if the strategy ever has no move."""
    n = 1 << k
    r = m0 % n if k else 0
    i = next(i for i in range(len(L)) if P[r][i])
    a = (P[r][i][0][0] + P[r][i][0][1]) / 2
    m, scale = m0, ONE
    for _ in range(steps):
        d = HALF if m % 2 else F(0)
        moved = False
        for j in range(len(L)):
            D = L[i] - 2 * L[j] / 3
            if D < 0:
                continue
            w = 2 * L[j] / 3
            for J in range(5):
                m1 = (3 * m) // 2 + J
                r1 = m1 % n if k else 0
                for lo, hi in P[r1][j]:
                    # u with c = 1.5u + d in [J + lo, J + hi], u in [a, a + D], [u, u + w] in an arc lift
                    for g0, g1 in arc_u(s, t, w):
                        u0 = max((J + lo - d) / F(3, 2), a, g0)
                        u1 = min((J + hi - d) / F(3, 2), a + D, g1)
                        if u0 < u1:
                            u = (u0 + u1) / 2
                            c = F(3, 2) * u + d
                            m, a, i, scale = m1, c - J, j, scale * F(3, 2)
                            moved = True
                            break
                    if moved:
                        break
                if moved:
                    break
            if moved:
                break
        if not moved:
            raise RuntimeError("strategy stuck")
    return (m + a) / scale


def dist_int(x):
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)


def nonempty(P):
    return any(P)


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "certificate":
        # arc_trap_k.py certificate K BETA_NUM/BETA_DEN NL OUT.json : symmetric arc [beta, 1-beta]
        import json
        k, beta, nl, out = int(argv[1]), F(argv[2]), int(argv[3]), argv[4]
        t = 1 - 2 * beta
        for j in range(1, nl):
            l = t * F(j, nl)
            P, fixed = solve(k, beta, t, l)
            if fixed and nonempty(P):
                json.dump({"k": k, "s": str(beta), "t": str(t), "l": str(l),
                           "P": [[[str(lo), str(hi)] for lo, hi in Pr] for Pr in P]},
                          open(out, "w"), indent=1)
                print(f"certificate written: k={k} beta={beta} l={l} -> {out}")
                return 0
        print("no certificate")
        return 1
    if argv[0] == "vw-certificate":
        # arc_trap_k.py vw-certificate K BETA W_LO W_HI W_DEN OUT.json : relaxed game, one width scanned
        import json
        k, beta = int(argv[1]), F(argv[2])
        w_lo, w_hi, w_den, out = int(argv[3]), int(argv[4]), int(argv[5]), argv[6]
        t = 1 - 2 * beta
        for wn in range(w_lo, w_hi):
            L = [F(wn, w_den)]
            P, fixed = solve_vw(k, beta, t, L)
            if fixed and any(x for row in P for x in row):
                json.dump({"game": "relaxed", "k": k, "s": str(beta), "t": str(t), "L": [str(x) for x in L],
                           "P": [[[[str(lo), str(hi)] for lo, hi in x] for x in row] for row in P]},
                          open(out, "w"), indent=1)
                print(f"certificate written: relaxed k={k} beta={beta} L={L[0]} -> {out}")
                return 0
        print("no certificate")
        return 1
    if argv[0] == "check":
        k, s, t, l = int(argv[1]), F(argv[2]), F(argv[3]), F(argv[4])
        P, fixed = solve(k, s, t, l)
        print(f"k={k} fixed={fixed} nonempty={nonempty(P)} residues_alive={sum(1 for x in P if x)}")
        return 0
    print(__doc__)
    return 2


# ---- persistent suite ----

def test_k0_matches_robust_game():
    # Pollington's arc is winnable blind; the FLP-forbidden short arc is not
    P, fx = solve(0, F(4, 65), F(57, 65), F(1, 5))
    assert fx and nonempty(P)
    P, fx = solve(0, F(1, 7), F(3, 10), F(1, 20))
    assert fx and not nonempty(P)


def test_awareness_never_hurts():
    # more memory can only enlarge the winning region (monotone in k)
    for k in range(4):
        P0, _ = solve(k, F(7, 80), F(33, 40), F(99, 800))
        P1, _ = solve(k + 1, F(7, 80), F(33, 40), F(99, 800))
        assert (not nonempty(P0)) or nonempty(P1)


def _wins_vw(k, beta, L):
    P, fx = solve_vw(k, beta, 1 - 2 * beta, L)
    return fx and any(x for row in P for x in row)


def test_relaxed_dominates_window_in_arc():
    # a window-in-arc certificate is a post-fixed point of the relaxed step, so the relaxed game wins too
    b, l = F(1227, 10000), F(26411, 300000)
    P, fx = solve(2, b, 1 - 2 * b, l)
    assert fx and nonempty(P)
    assert _wins_vw(2, b, [l])


def test_relaxed_respects_flp():
    # soundness control: Flatto-Lagarias-Pollington forbid every arc shorter than 1/3
    for k in (0, 2):
        for w in (F(1, 50), F(1, 20), F(1, 10)):
            P, fx = solve_vw(k, F(1, 7), F(3, 10), [w])
            assert fx and not any(x for row in P for x in row)


def test_relaxed_certificate_orbits_stay_far():
    # independent exact arithmetic: play the memoryless certificate against true integer parts;
    # every orbit must keep ||xi (3/2)^n|| >= beta = 0.1228 (the target, set by hand)
    b, w = F(307, 2500), F(123, 1000)
    P, fx = solve_vw(0, b, 1 - 2 * b, [w])
    assert fx and P[0][0]
    for m0 in (1, 2, 3, 100):
        xi = vw_orbit(P, 0, b, 1 - 2 * b, [w], m0, 120)
        assert xi > 0
        assert min(dist_int(xi * F(3, 2) ** n) for n in range(120)) >= b


def test_relaxed_edge_regression():
    # regression of the measured edge (tool output, not ground truth): 7/57 - 1e-6 wins, 7/57 + 1e-6 fails
    assert _wins_vw(0, F(7, 57) - F(1, 10 ** 6), [F(123, 1000)])
    assert not any(_wins_vw(0, F(7, 57) + F(1, 10 ** 6), [F(j, 200)]) for j in range(16, 30))


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
