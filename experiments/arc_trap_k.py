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
    arc_trap_k.py test
"""
from __future__ import annotations

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


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
