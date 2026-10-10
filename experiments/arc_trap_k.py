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


def complement01(ivs):
    """[0, 1) minus a normalized interval union (closed endpoints kept on both sides: a superset, so
    it is only used as a cap, never as a certificate)."""
    out, x = [], F(0)
    for lo, hi in norm(ivs):
        if lo > x:
            out.append((x, lo))
        x = max(x, hi)
    if x < ONE:
        out.append((x, ONE))
    return out


def solve_vw(k, s, t, L, iters=5000, N=1 << 24, forbidden=(), trace=None, cap=None):
    """Greatest post-fixed point on the 1/N lattice: the sets only shrink and the lattice is finite, so
    this terminates; the result satisfies P <= step(P), which is all soundness needs.  `forbidden`
    residues start empty, so the result is the largest strategy that avoids them (KRelaxedLiveEverywhere
    asks whether that is always empty).  `trace`, a list, collects the live residues per iteration."""
    n, q = 1 << k, len(L)
    P = [[[] if r in forbidden else list((cap or {}).get(r, [(F(0), ONE)])) for _ in range(q)]
         for r in range(n)]
    for _ in range(iters):
        if trace is not None:
            trace.append([r for r in range(n) if any(P[r])])
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


def saturate_vw(P, k, s, t, L, rounds=200, N=1 << 20, trace=None):
    """Predecessor saturation (ArcReview.saturate): repeatedly add every start with a legal move whose
    both top-bit children lie in the current set.  Starting from a post-fixed point, every stage is one
    (new starts move into the old set), so the limit is a strategy.  `trace` collects the good-base
    count per round."""
    n, q = 1 << k, len(L)
    for _ in range(rounds):
        if trace is not None:
            trace.append(len(good_bases(P, k)) if k >= 1 else None)
        new = []
        for r in range(n):
            d = HALF if r % 2 else F(0)
            row = []
            for i in range(q):
                acc = norm(sum((vw_aset(P, r, k, i, j, d, s, t, L) for j in range(q)), []))
                row.append(norm(P[r][i] + round_in(acc, N)))
            new.append(row)
        if new == P:
            return P, True
        P = new
    return P, False


def split_seeds(k, s, t, L, xs=(F(1, 4), F(1, 2), F(3, 4)), N=1 << 20):
    """Overlap-breaking seeds: for each base b of the greatest fixed point G, split the shared starts
    C = G(b) ∩ G(b + 2^(k-1)) at x, cap each lift away from one side, and descend.  Yields
    (b, x, Q) for every result with both lifts live and base b NOT good (none seen through k = 5)."""
    h = 1 << (k - 1)
    G, _ = solve_vw(k, s, t, L, N=N)
    if not nonempty(G):
        return
    for b in range(h):
        C = inter(G[b][0], G[b + h][0])
        for x in xs:
            lo, hi = inter(C, [(F(0), x)]), inter(C, [(x, ONE)])
            for cb, ch in ((hi, lo), (lo, hi)):
                cap = {b: inter(G[b][0], complement01(cb)), b + h: inter(G[b + h][0], complement01(ch))}
                Q, _ = solve_vw(k, s, t, L, N=N, cap=cap)
                if Q[b][0] and Q[b + h][0] and b not in good_bases(Q, k):
                    yield b, x, Q


def lift_witnesses(k, s, t, l, N=1 << 20):
    """Per base b of the greatest fixed point (one width l): the exact usable-u sets of both lifts (legal
    moves into both top-bit children, u reachable from a start in [0, 1)), the nearest pair (u, v), its
    gap, one shared start a, and each move's floor and successor base.  ArcOverlap.sharedStart_iff
    consumes the minimal gap: a shared start exists iff it is at most l/3."""
    L = [l]
    G, _ = solve_vw(k, s, t, L, N=N)
    h = 1 << (k - 1)
    out = []
    for b in range(h):
        sets = []
        for r in (b, b + h):
            d = HALF if r % 2 else F(0)
            sets.append(inter(vw_good_u(G, r, k, 0, d, s, t, L), [(F(0), 1 + l / 3)]))
        best = None
        for u0, u1 in sets[0]:
            for v0, v1 in sets[1]:
                if max(u0, v0) <= min(u1, v1):
                    u = v = max(u0, v0)
                elif u1 < v0:
                    u, v = u1, v0
                else:
                    u, v = u0, v1
                if best is None or abs(u - v) < abs(best[0] - best[1]):
                    best = (u, v)
        rec = {"base": b, "usable_u": [[[str(x), str(y)] for x, y in S] for S in sets]}
        if best:
            u, v = best
            a_lo, a_hi = max(max(u, v) - l / 3, F(0)), min(min(u, v), ONE)
            moves = []
            for r, w in ((b, u), (b + h, v)):
                d = HALF if r % 2 else F(0)
                c = F(3, 2) * w + d
                J = c.numerator // c.denominator
                moves.append({"residue": r, "u": str(w), "floor": J,
                              "successor_base": ((3 * r - r % 2) // 2 + J) % h})
            rec.update(gap=str(abs(u - v)), gap_over_l=float(abs(u - v) / l),
                       shared_a=str(a_lo) if a_lo <= a_hi else None, moves=moves)
        out.append(rec)
    return out


def fatten_residue(P, k, e):
    """ArcFattening's e/2 scheme in residue form (first width only): start y = x - e/2 + z with
    |z| <= e/12.  A start pushed below its integer part moves to residue r - 1 with fraction + 1."""
    n = 1 << k
    out = [[] for _ in range(n)]
    for r in range(n):
        for lo, hi in P[r][0]:
            a, b = lo - e / 2 - e / 12, hi - e / 2 + e / 12
            if b > 0:
                out[r].append((max(a, F(0)), b))
            if a < 0:
                out[(r - 1) % n].append((a + 1, min(b, F(0)) + 1))
    return [[norm(x)] for x in out]


def rounded_post_fixed_failures(P, k, s, t, L, N):
    """Residues where P is NOT inside solve_vw's rounded step of itself (empty list: P is a lattice
    post-fixed point, so solve_vw's greatest fixed point contains it)."""
    bad = []
    for r in range(1 << k):
        d = HALF if r % 2 else F(0)
        acc = round_in(norm(sum((vw_aset(P, r, k, 0, j, d, s, t, L) for j in range(len(L))), [])), N)
        if inter(norm(P[r][0]), acc) != norm(P[r][0]):
            bad.append(r)
    return bad


def width_sweep(k, beta, e0, step, N):
    """The finite computation behind ArcSolverInclusion.no_kRelaxedStrategy_7_57_plus: solve the
    symmetric arc widened to beta' = beta - e0/2 at every width i*step <= 3t'/2 (step <= e0/2 for the
    width net).  Returns the widths whose lattice fixed point is nonempty or unconverged (empty list:
    no winner, given the fattening and bridge hypotheses)."""
    bp = beta - e0 / 2
    tp = 1 - 2 * bp
    out, l = [], step
    while l <= F(3, 2) * tp:
        P, fx = solve_vw(k, bp, tp, [l], N=N)
        if not fx or nonempty(P):
            out.append(l)
        l += step
    return out


def solver_step(P, r, k, s, t, L):
    """The un-rounded step solve_vw applies at residue r (first width): starts with a good u."""
    d = HALF if r % 2 else F(0)
    return norm(sum((vw_aset(P, r, k, 0, j, d, s, t, L) for j in range(len(L))), []))


def brute_open_move(P, r, k, s, t, l, a, mu, grid=400):
    """Independent check of ArcSolverInclusion.stepOpen in residue form: search u = a + i*(l/3)/grid
    for a move whose whole interval [u - mu, u + mu] (sampled at 5 points) is legal, inside an arc lift,
    and lands in BOTH top-bit children.  Written without the solver's interval code."""
    n, half = 1 << k, 1 << (k - 1)
    d = HALF if r % 2 else F(0)
    w = 2 * l / 3

    def ok(u):
        if not (a <= u and u + w <= a + l):
            return False
        if not any(m + s <= u and u + w <= m + s + t for m in range(-1, 5)):
            return False
        c = F(3, 2) * u + d
        J = c.numerator // c.denominator
        fr = c - J
        base = ((3 * r - r % 2) // 2 + J) % half
        return all(any(lo <= fr <= hi for lo, hi in P[base + b * half][0]) for b in (0, 1))

    for i in range(grid + 1):
        u = a + (l / 3) * F(i, grid)
        if all(ok(u + mu * F(q, 2)) for q in (-2, -1, 0, 1, 2)):
            return True
    return False


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


def carry_avoidable(k, forbidden, shs=(0, 1, 2)):
    """Residues from which a constructor that picks its floor sh freely per residue keeps every live
    residue out of `forbidden` forever.  Both top-bit children of the next base must stay live (greatest
    fixed point of a safety game).  Nonempty means carry combinatorics alone cannot force liveness at
    `forbidden`."""
    mod, half = 1 << k, 1 << (k - 1)
    W = set(range(mod)) - set(forbidden)
    while True:
        W2 = {r for r in W if any(
            (b := ((3 * r - r % 2) // 2 + sh) % half if half > 1 else 0) in W and b + half in W
            for sh in shs)}
        if W2 == W:
            return W
        W = W2


def nonempty(P):
    return any(x for row in P for x in row)


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
    if argv[0] == "carry-avoid":
        # arc_trap_k.py carry-avoid KMAX : how many classes m (pairs {m, m+1}) a free-floor constructor avoids
        for k in range(1, int(argv[1]) + 1):
            mod = 1 << k
            one = sum(1 for m in range(mod) if carry_avoidable(k, {m}))
            two = sum(1 for m in range(mod) if carry_avoidable(k, {m, (m + 1) % mod}))
            print(f"k={k}: avoidable classes {one}/{mod}, avoidable pairs {two}/{mod}")
        return 0
    if argv[0] == "live-forbid":
        # live-forbid K S T JLO JHI JSTEP: for each winning width t*j/400, the residues m such that some
        # strategy avoids class m (KRelaxedLiveEverywhere predicts none)
        k, s, t = int(argv[1]), F(argv[2]), F(argv[3])
        for j in range(int(argv[4]), int(argv[5]) + 1, int(argv[6])):
            L = [t * F(j, 400)]
            P, fx = solve_vw(k, s, t, L, N=1 << 20)
            live = [r for r in range(1 << k) if P[r][0]]
            if not (fx and live):
                continue
            dodge = [m for m in range(1 << k) if nonempty(solve_vw(k, s, t, L, N=1 << 20, forbidden={m})[0])]
            print(f"j {j} live {live} dodgeable {dodge}", flush=True)
        return 0
    if argv[0] == "witnesses":
        # witnesses K S T J OUT.json : lift_witnesses for width t*J/400 (exact rationals as strings)
        import json
        k, S, T, j = int(argv[1]), F(argv[2]), F(argv[3]), int(argv[4])
        w = lift_witnesses(k, S, T, T * F(j, 400))
        with open(argv[5], "w") as fh:
            json.dump({"k": k, "s": str(S), "t": str(T), "l": str(T * F(j, 400)), "bases": w}, fh, indent=1)
        print(f"{len(w)} bases, max gap/l {max(x.get('gap_over_l', 9) for x in w):.3f}")
        return 0
    if argv[0] == "width-sweep":
        # width-sweep KMAX BETA E0 STEP LOGN [KMIN] : width_sweep for k = KMIN..KMAX
        beta, e0, step, N = F(argv[2]), F(argv[3]), F(argv[4]), 1 << int(argv[5])
        kmin = int(argv[6]) if len(argv) > 6 else 1
        for k in range(kmin, int(argv[1]) + 1):
            print(f"k {k} nonempty widths {[str(x) for x in width_sweep(k, beta, e0, step, N)]}", flush=True)
        return 0
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


def test_memory_helps_off_centre():
    # 2026-10-06: off the symmetric position memory does help.  Arc [2/5, 2/5 + 87/100]: k = 3 wins,
    # k = 0..2 lose at every width t*j/400, j = 5, 8, ..., 398 (full scan in the research note; here
    # the band around the k = 3 winners).  Tool output, recorded as a regression.
    s, t = F(2, 5), F(87, 100)
    assert _wins_vw_s(3, s, t, [t * F(86, 400)])
    assert not any(_wins_vw_s(2, s, t, [t * F(j, 400)]) for j in range(77, 125, 3))


def test_live_everywhere_off_centre():
    # KRelaxedLiveEverywhere evidence (2026-10-07, tool output as regression): the off-centre k = 3
    # winner's greatest fixed point is live at every residue, never at only some
    s, t = F(2, 5), F(87, 100)
    P, fx = solve_vw(3, s, t, [t * F(86, 400)], N=1 << 20)
    assert fx and all(row[0] for row in P)


def _wins_vw_s(k, s, t, L):
    P, fx = solve_vw(k, s, t, L, N=1 << 20)
    return fx and any(x for row in P for x in row)

def test_carries_alone_cannot_force_liveness():
    # k = 1, 2: the free-floor constructor cannot dodge an adjacent pair; from k = 3 it dodges everything
    assert not carry_avoidable(2, {0, 1}) and carry_avoidable(2, {0})
    for k in (3, 6):
        assert all(carry_avoidable(k, {m, (m + 1) % (1 << k)}) for m in range(1 << k))


def test_forbidding_any_class_kills_the_strategy():
    # 2026-10-09, geometric liveness: the k = 3 off-centre winners admit no strategy avoiding any one
    # class, though the carry game with a free floor in {0, 1} dodges every class from k = 4 on
    s, t = F(2, 5), F(87, 100)
    L = [t * F(86, 400)]
    assert nonempty(solve_vw(3, s, t, L, N=1 << 20)[0])
    assert not any(nonempty(solve_vw(3, s, t, L, N=1 << 20, forbidden={m})[0]) for m in range(8))
    assert all(carry_avoidable(4, {m}, shs=(0, 1)) for m in range(16))


def test_strong_liveness_fails_at_k6():
    # 2026-10-09: not_kRelaxedLiveEverywhereStrong.  A k = 6 strategy live at 63 of 64 classes (dead only
    # at 27 = -5 mod 32), while the greatest fixed point is live at all 64 (the weak form survives)
    s, t = F(2, 5), F(87, 100)
    L = [t * F(100, 400)]
    P, fx = solve_vw(6, s, t, L, N=1 << 20)
    assert fx and all(P[r][0] for r in range(64))
    Q, fx = solve_vw(6, s, t, L, N=1 << 20, forbidden={27})
    assert fx and [r for r in range(64) if not Q[r][0]] == [27]
    for m0 in (64 + 1, 64 * 7 + 26, 64 * 123 + 59):
        vw_orbit(Q, 6, s, t, L, m0, 60)


def good_bases(P, k):
    """Bases b < 2^(k-1) whose two lifts share a start (KRelaxedAllBasesGood, first width)."""
    h = 1 << (k - 1)
    return [b for b in range(h) if inter(P[b][0], P[b + h][0])]


def test_all_bases_good_but_the_dodge_lacks_one():
    # 2026-10-09: the greatest fixed point has every base good; the k = 6 dodge lacks exactly base 27
    s, t = F(2, 5), F(87, 100)
    L = [t * F(100, 400)]
    assert len(good_bases(solve_vw(6, s, t, L, N=1 << 20)[0], 6)) == 32
    Q = solve_vw(6, s, t, L, N=1 << 20, forbidden={27, 59})[0]
    assert sorted(set(range(32)) - set(good_bases(Q, 6))) == [27]


def test_saturation_restores_the_dodged_base():
    # 2026-10-09, ArcReview.PredecessorSaturationAllBases first control: one predecessor layer over the
    # k = 6 dodge (base 27 missing) makes every base good again
    s, t = F(2, 5), F(87, 100)
    L = [t * F(100, 400)]
    Q = solve_vw(6, s, t, L, N=1 << 20, forbidden={27, 59})[0]
    tr = []
    S, fx = saturate_vw(Q, 6, s, t, L, rounds=2, trace=tr)
    assert tr == [31, 32]


def test_breaking_a_shared_start_kills_a_lift():
    # 2026-10-09 (with Astra): capping the two lifts of a base onto opposite sides of their shared starts
    # never leaves both live without a shared start (k = 3..5 sweep: 0 seeds); here the k = 3 winner
    s, t = F(2, 5), F(87, 100)
    assert list(split_seeds(3, s, t, [t * F(86, 400)])) == []
    G = solve_vw(3, s, t, [t * F(86, 400)], N=1 << 20)[0]
    assert len(good_bases(G, 3)) == 4  # the control: the uncapped winner has every base good


def test_lift_witnesses_meet_the_overlap_criterion():
    # Astra's request 2026-10-09: k = 4, arc (1/2, 9/10), j = 64 (no class good at level k - 2).  Every
    # base's nearest usable pair is within l/3 and comes with a shared start in [0, 1)
    s, t = F(1, 2), F(9, 10)
    l = t * F(64, 400)
    w = lift_witnesses(4, s, t, l)
    assert len(w) == 8 and all(F(x["gap"]) <= l / 3 and x["shared_a"] is not None for x in w)


def test_fattened_winner_is_inside_the_rounded_solver():
    # 2026-10-10, solver-inclusion step of the fattening completeness route (with Astra): the fattened
    # k = 3 winner at arc widened by e/2 per end, width l + e, is a post-fixed point of the rounded step,
    # so the solver's greatest fixed point contains it; the UNfattened winner there is not (teeth)
    s, t, k, N = F(2, 5), F(87, 100), 3, 1 << 20
    l, e = t * F(86, 400), F(1, 100)
    G = solve_vw(k, s, t, [l], N=N)[0]
    Fz = [[round_in(x[0], N)] for x in fatten_residue(G, k, e)]
    s2, t2, L2 = s - e / 2, t + e, [l + e]
    assert rounded_post_fixed_failures(Fz, k, s2, t2, L2, N) == []
    G2 = solve_vw(k, s2, t2, L2, N=N)[0]
    assert all(inter(Fz[r][0], G2[r][0]) == Fz[r][0] for r in range(8))
    assert rounded_post_fixed_failures(G, k, s2, t2, L2, N) != []
    # a grid too coarse for the margin (e N / 24 << 1) breaks inclusion
    e = F(1, 10 ** 5)
    Fz = [[round_in(x[0], 1 << 16)] for x in fatten_residue(G, k, e)]
    assert rounded_post_fixed_failures(Fz, k, s - e / 2, t + e, [l + e], 1 << 16) != []


def test_width_sweep_above_7_57_is_empty_with_a_live_control():
    # 2026-10-10 (no_kRelaxedStrategy_7_57_plus): k = 1 is empty over the full width net just above 7/57,
    # while the same solver finds a k = 1 winner just below it (the control that gives the sweep teeth)
    assert width_sweep(1, F(7, 57) + F(1, 1000), F(1, 1000), F(1, 2500), 1 << 17) == []
    b = F(7, 57) - F(1, 10 ** 4)
    assert any(nonempty(solve_vw(1, b, 1 - 2 * b, [F(j, 1000)], N=1 << 15)[0]) for j in range(100, 140))


def test_solver_step_contains_open_moves():
    # 2026-10-10, hypothesis (c) of ArcSolverInclusion.no_kRelaxedStrategy_7_57_plus: every start the
    # brute-force search finds an open move for is in solve_vw's step.  Random lattice strategies at k = 2, 3;
    # also count the converse direction so the check is not vacuous
    import random
    rng = random.Random(4)
    s, t = F(2, 5), F(87, 100)
    found = 0
    for k in (2, 3):
        l = t * F(86, 400)
        for _ in range(6):
            P = [[norm([(F(a, 64), F(a + rng.randint(2, 24), 64)) for a in rng.sample(range(64), 3)])]
                 for _ in range(1 << k)]
            for r in range(1 << k):
                acc = solver_step(P, r, k, s, t, [l])
                for _ in range(8):
                    a = F(rng.randint(0, 999), 1000)
                    if brute_open_move(P, r, k, s, t, l, a, F(1, 10 ** 4), grid=60):
                        found += 1
                        assert any(lo <= a <= hi for lo, hi in acc)
    assert found >= 20


def _rust(*args):
    """Run the independent Rust re-implementation (experiments/arc_sweep_rs), building it if needed."""
    import pathlib
    crate = pathlib.Path(__file__).parent / "arc_sweep_rs"
    subprocess.run(["cargo", "build", "--release", "--quiet"], cwd=crate, check=True)
    out = subprocess.run([str(crate / "target/release/arc_sweep"), *map(str, args)], capture_output=True,
                         text=True, check=True)
    return out.stdout


def test_rust_agrees_with_python():
    # 2026-10-10: a second instrument written from the Lean spec (stepOpen, roundIn), not from this file.
    # Known winner / loser / just-below-7/57 controls, then the k = 1 sweep above 7/57
    l = F(87, 100) * F(86, 400)
    assert "live [0, 1, 2, 3, 4, 5, 6, 7]" in _rust("solve", 3, "2/5", "87/100", l, 20)
    assert "live []" in _rust("solve", 2, "2/5", "87/100", l, 20)
    b = F(7, 57) - F(1, 10 ** 4)
    assert "live [0, 1]" in _rust("solve", 1, b, 1 - 2 * b, "123/1000", 15)
    assert "nonempty []" in _rust("sweep", 1, 1, "7057/57000", "1/1000", "1/2500", 17)



def test_rust_round_keeps_cell_ending_at_hi():
    # Astra's hand-computed regression (2026-10-10).  Open start interval (1/8, 3/4), N = 4: the half-open
    # cells inside are [1/4, 1/2) and [1/2, 3/4), so the closed output is [(1/4, 3/4)].  The old upper
    # index ceil(hi N) - 1 = 2 returned only [(1/4, 1/2)], an under-inclusion (unsafe for emptiness).
    assert _rust("round", 2, "1/8", "3/4").split() == ["(1/4,3/4)"]
    # teeth: a cell crossing hi is not kept, and a cell starting at lo > 0 is not kept
    assert _rust("round", 2, "1/8", "7/10").split() == ["(1/4,1/2)"]
    assert _rust("round", 2, "1/4", "3/4").split() == ["(1/2,3/4)"]
    # the clip point 0 keeps its first cell
    assert _rust("round", 2, "0", "1/2").split() == ["(0/1,1/2)"]


def _rust_nocarry(*args):
    import os
    os.environ["ARC_NOCARRY"] = "1"
    try:
        return _rust(*args)
    finally:
        del os.environ["ARC_NOCARRY"]


def test_delay_game_controls():
    # ArcDelayGame.KDelayStrategy (2026-10-10): the pure delay game, residue = next k parities, no carry.
    # Off-centre sibling: lookahead alone gives the memory benefit (k = 2 loses, k = 3 wins).
    l = F(87, 100) * F(86, 400)
    assert "live []" in _rust_nocarry("solve", 2, "2/5", "87/100", l, 20)
    assert "live [0, 1, 2, 3, 4, 5, 6, 7]" in _rust_nocarry("solve", 3, "2/5", "87/100", l, 20)
    # teeth: the games differ.  k = 4, arc [1/20, 1/20 + 79/100], width 1501/8000 (found by a 60-arc random
    # scan, the only disagreement): the delay game wins, the k-memory game loses
    assert "live []" in _rust("solve", 4, "1/20", "79/100", "1501/8000", 14)
    assert "live [0, 1, 2" in _rust_nocarry("solve", 4, "1/20", "79/100", "1501/8000", 14)
    # positive control below 7/57
    b = F(7, 57) - F(1, 10 ** 5)
    assert "live [0, 1, 2, 3]" in _rust_nocarry("solve", 2, b, 1 - 2 * b, "1225/10000", 15)
    # above 7/57 the delay game also empties (k = 2, the full sweep is in ArcDelayGame's docstring)
    assert "nonempty []" in _rust_nocarry("sweep", 2, 2, "7057/57000", "1/1000", "1/2500", 17)


def test_upper_edge_memoryless():
    # ArcDelayGame.KRelaxedUpperEdgeMemoryless (2026-10-10): on [beta, 1 - beta] the widest winning width does
    # not move with memory.  beta = 0.12: 0.1495 wins and 0.1505 loses, at k = 1 and at k = 4
    for k in (1, 4):
        assert "live []" not in _rust("solve", k, "3/25", "19/25", "299/2000", 16)
        assert "live []" in _rust("solve", k, "3/25", "19/25", "301/2000", 16)
    # teeth: the same check fails in the pure delay game.  beta = 0.1, width 0.31 is far above the k-memory
    # upper edge 0.262 (k = 1 and k = 6 lose), but the delay game wins there at k = 6 (not at k = 4)
    for k in (1, 6):
        assert "live []" in _rust("solve", k, "1/10", "4/5", "31/100", 16)
    assert "live []" in _rust_nocarry("solve", 4, "1/10", "4/5", "31/100", 16)
    assert "live []" not in _rust_nocarry("solve", 6, "1/10", "4/5", "31/100", 16)

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
