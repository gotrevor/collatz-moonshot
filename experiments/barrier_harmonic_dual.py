#!/usr/bin/env -S uv run --quiet python3
"""Harmonic (alpha = 1) dual obstruction for the uniform local certificate.

At ternary depth ``k`` with a fixed set of height floors, the shared-lift
operator of ``barrier_transfer.build_correlated_height_transitions`` gives every
source state ``s`` three alternatives, one per unknown next ternary digit
``t in {0,1,2}``.  At harmonic weight ``alpha = 1`` alternative ``t`` acts by

    (M_{k,t} V)(s) = sum_{(j,u) in edges(s,t)} (3 / 2^j) V(u).

A *positive harmonic local certificate* is a positive ``V`` with

    V(s) < (M_{k,t} V)(s)      for every state s and every lift t.        (H)

Because the certificate must satisfy *every* alternative, choosing any single
policy ``tau : S_k -> {0,1,2}`` (one alternative per row) yields the necessary
condition ``V < M_{k,tau} V`` componentwise.  If a strictly positive left weight
``pi`` satisfies the *dual contraction*

    (M_{k,tau}^T pi)(u) < pi(u)     for every state u,                    (D)

then summing (H) against ``pi`` gives

    pi . V  <  pi . (M_{k,tau} V)  =  (M_{k,tau}^T pi) . V  <  pi . V,

a contradiction.  Hence (D) for one policy *rules out* every positive harmonic
certificate at depth ``k``.  This script constructs such policies and duals and
verifies (D) by *exact rational arithmetic* (the verifier, not the eigensolver,
is authoritative).

The engineering question this probes: is the obstruction *depth-uniform*?  The
constant lift-digit-1 policy has spectral radius stable near 0.933 through depth
10; if that survives richer child sets and taller height grids it is a candidate
for a depth-independent structural theorem, not a lucky finite table.

Examples:
    uv run --quiet python3 experiments/barrier_harmonic_dual.py
    uv run --quiet python3 experiments/barrier_harmonic_dual.py --depths 8,9,10 \
        --policy const1
    uv run --quiet python3 experiments/barrier_harmonic_dual.py --depths 6 \
        --policy min --children 9
    uv run --quiet python3 experiments/barrier_harmonic_dual.py --depths 6 \
        --policy const1 --heights 1,7/4,3,6,12,24,48
"""

from __future__ import annotations

import argparse
from fractions import Fraction

from barrier_transfer import (
    CORRELATED_THREE_QUARTERS_HEIGHT_BINS,
    build_correlated_height_transitions,
)

# transitions[s] = tuple of 3 alternatives; alternative = tuple of (cost, target).
Transitions = tuple[tuple[tuple[tuple[int, int], ...], ...], ...]


def harmonic_coefficient(cost: int) -> Fraction:
    """Exact harmonic edge weight ``3 / 2^cost``."""
    return Fraction(3, 2**cost)


def alternative_row(alternative: tuple[tuple[int, int], ...]) -> dict[int, Fraction]:
    """Collapse one alternative's edges into ``target -> summed coefficient``."""
    row: dict[int, Fraction] = {}
    for cost, target in alternative:
        row[target] = row.get(target, Fraction(0)) + harmonic_coefficient(cost)
    return row


def policy_matrix(
    transitions: Transitions, policy: tuple[int, ...]
) -> list[dict[int, Fraction]]:
    """Exact sparse ``M_{k,tau}`` as one summed row per state."""
    return [
        alternative_row(transitions[s][policy[s]]) for s in range(len(transitions))
    ]


def apply_matrix(matrix: list[dict[int, Fraction]], vector: list[Fraction]) -> list[Fraction]:
    return [
        sum((coeff * vector[u] for u, coeff in row.items()), Fraction(0))
        for row in matrix
    ]


def apply_transpose(
    matrix: list[dict[int, Fraction]], vector: list[Fraction]
) -> list[Fraction]:
    result = [Fraction(0)] * len(vector)
    for s, row in enumerate(matrix):
        vs = vector[s]
        for u, coeff in row.items():
            result[u] += coeff * vs
    return result


# ---------------------------------------------------------------------------
# Policies
# ---------------------------------------------------------------------------


def constant_policy(transitions: Transitions, digit: int) -> tuple[int, ...]:
    if digit not in range(3):
        raise ValueError("constant lift digit must be 0, 1, or 2")
    return tuple(digit for _ in transitions)


def minimizing_policy(
    transitions: Transitions, iterations: int
) -> tuple[tuple[int, ...], float, float]:
    """Fixed policy read off the nonlinear min-harmonic eigenvector.

    Iterate ``(TV)(s) = min_t (M_{k,t} V)(s)`` in float, normalize, then read the
    argmin alternative per row.  Returns the policy and the last ratio bounds.
    """
    n = len(transitions)
    # Precompute float rows per alternative.
    float_alts: list[list[list[tuple[float, int]]]] = []
    for alternatives in transitions:
        row_alts: list[list[tuple[float, int]]] = []
        for alt in alternatives:
            acc: dict[int, float] = {}
            for cost, target in alt:
                acc[target] = acc.get(target, 0.0) + 3.0 / 2.0**cost
            row_alts.append([(c, u) for u, c in acc.items()])
        float_alts.append(row_alts)

    weights = [1.0] * n
    lower = upper = 1.0
    policy = tuple(0 for _ in range(n))
    for _ in range(iterations):
        image = [0.0] * n
        choice = [0] * n
        for s in range(n):
            best = None
            best_t = 0
            for t, edges in enumerate(float_alts[s]):
                val = sum(c * weights[u] for c, u in edges)
                if best is None or val < best:
                    best = val
                    best_t = t
            image[s] = best  # type: ignore[assignment]
            choice[s] = best_t
        ratios = [img / w for img, w in zip(image, weights)]
        lower, upper = min(ratios), max(ratios)
        # geometric renormalization
        from math import exp, log

        scale = exp(sum(log(v) for v in image) / n)
        weights = [(w * (img / scale)) ** 0.5 for w, img in zip(weights, image)]
        policy = tuple(choice)
        if upper - lower < 1e-13:
            break
    return policy, lower, upper


# ---------------------------------------------------------------------------
# Spectral radius bounds (Collatz) for a fixed policy matrix
# ---------------------------------------------------------------------------


def spectral_bounds(
    matrix: list[dict[int, Fraction]], iterations: int
) -> tuple[float, float, list[float]]:
    """Collatz lower/upper bounds for the (nonneg) fixed matrix, in float."""
    n = len(matrix)
    fmatrix = [[(float(c), u) for u, c in row.items()] for row in matrix]
    v = [1.0] * n
    lo = hi = 0.0
    for _ in range(iterations):
        img = [sum(c * v[u] for c, u in row) for row in fmatrix]
        # guard: a zero row would break the ratio; policy rows are nonempty.
        ratios = [i / w for i, w in zip(img, v)]
        lo, hi = min(ratios), max(ratios)
        m = max(img)
        if m == 0:
            break
        v = [i / m for i in img]
        if hi - lo < 1e-14:
            break
    return lo, hi, v


# ---------------------------------------------------------------------------
# Exact left dual: solve pi = 1 + M^T pi (Neumann), round to integers, verify.
# ---------------------------------------------------------------------------


def build_left_dual(
    matrix: list[dict[int, Fraction]],
    iterations: int,
    denom_pow: int,
) -> tuple[list[int], int, Fraction, bool]:
    """Construct and *exactly verify* a positive integer left dual.

    Numerically solve ``pi = 1 + M^T pi`` (converges iff spectral radius < 1),
    round each component *up* to the common denominator ``2^denom_pow``, and
    check the strict contraction ``(M^T pi)(u) < pi(u)`` for every ``u`` with
    exact rational arithmetic.  Returns (integer numerators over 2^denom_pow,
    denom_pow, worst slack, all_ok).
    """
    n = len(matrix)
    # Neumann iteration in float for speed, then snap to exact rationals.
    fmatrix = [[(float(c), u) for u, c in row.items()] for row in matrix]
    pi = [1.0] * n
    for _ in range(iterations):
        mtpi = [0.0] * n
        for s, row in enumerate(fmatrix):
            ps = pi[s]
            for c, u in row:
                mtpi[u] += c * ps
        new = [1.0 + mtpi[u] for u in range(n)]
        if max(abs(a - b) for a, b in zip(new, pi)) < 1e-12:
            pi = new
            break
        pi = new

    denom = 2**denom_pow
    # Round each component up to a multiple of 1/denom, and add a small cushion
    # so the strict inequality has room.  We then rescale to exact Fractions.
    numer = [max(1, int(p * denom) + 1) for p in pi]
    pi_exact = [Fraction(a, denom) for a in numer]
    mtpi_exact = apply_transpose(matrix, pi_exact)
    worst = None
    ok = True
    for u in range(n):
        slack = pi_exact[u] - mtpi_exact[u]  # want > 0
        if slack <= 0:
            ok = False
        if worst is None or slack < worst:
            worst = slack
    return numer, denom_pow, worst if worst is not None else Fraction(0), ok


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def finite_memory_supersolution(
    memory: int,
    heights: tuple[Fraction, ...],
    children: int,
    iterations: int,
    denom_pow: int,
) -> tuple[int, int, float, Fraction, bool]:
    """Depth-independent contraction from a ``(r mod 3^memory, floor)`` weight.

    Under the constant-lift-1 policy the harmonic edge coefficient depends only
    on ``(r mod 9, floor)`` and each child's residue mod ``3^memory`` is fixed by
    the source mod ``3^(memory+1)``.  Hence a weight ``w`` on the classes
    ``(r mod 3^memory, floor)`` acts on states of *every* depth ``k >= memory``
    through the *same* finite inequality set, indexed by ``s mod 3^(memory+1)``.
    We build that operator at depth ``d = memory+1``, find its Collatz right
    weight, snap it to integers over ``2^denom_pow``, and EXACTLY check

        (M w)(s) < w(class(s))   for every state s at depth d.

    If all hold, the pullback of ``w`` bounds ``M_k`` by the exact max ratio
    ``c < 1`` at *all* depths ``k >= memory`` — a single depth-uniform witness.
    Returns (num_classes, num_states, contraction_c_float, exact_c, all_ok).
    """
    d = memory + 1
    transitions = build_correlated_height_transitions(
        d, heights, children, include_shrinking=True
    )
    modulus = 3**d
    units = [v for v in range(modulus) if v % 3 != 0]
    ucount = len(units)
    lowmod = 3**memory
    lunits = [v for v in range(lowmod) if v % 3 != 0]
    lidx = {u: i for i, u in enumerate(lunits)}
    nclasses = len(lunits) * len(heights)

    def class_of(state: int) -> int:
        floor_index = state // ucount
        residue = units[state % ucount]
        return floor_index * len(lunits) + lidx[residue % lowmod]

    # Float rows (const-lift-1 = alternative index 1), collapsed to class targets.
    frows: list[tuple[int, list[tuple[int, float]]]] = []
    for s in range(len(transitions)):
        acc: dict[int, float] = {}
        for cost, target in transitions[s][1]:
            tc = class_of(target)
            acc[tc] = acc.get(tc, 0.0) + 3.0 / 2.0**cost
        frows.append((class_of(s), list(acc.items())))

    w = [1.0] * nclasses
    for _ in range(iterations):
        img = [0.0] * nclasses
        for sc, edges in frows:
            val = sum(c * w[t] for t, c in edges)
            if val > img[sc]:
                img[sc] = val
        m = max(img)
        new = [i / m for i in img]
        if max(abs(a - b) for a, b in zip(new, w)) < 1e-15:
            w = new
            break
        w = new

    denom = 2**denom_pow
    wq = [Fraction(max(1, round(x * denom)), denom) for x in w]
    worst_ratio = Fraction(0)
    ok = True
    for s in range(len(transitions)):
        acc_q: dict[int, Fraction] = {}
        for cost, target in transitions[s][1]:
            tc = class_of(target)
            acc_q[tc] = acc_q.get(tc, Fraction(0)) + Fraction(3, 2**cost)
        lhs = sum((c * wq[t] for t, c in acc_q.items()), Fraction(0))
        rhs = wq[class_of(s)]
        if lhs >= rhs:
            ok = False
        ratio = lhs / rhs
        if ratio > worst_ratio:
            worst_ratio = ratio
    return nclasses, len(transitions), float(worst_ratio), worst_ratio, ok


def parse_heights(text: str) -> tuple[Fraction, ...]:
    bins = tuple(Fraction(part) for part in text.split(",") if part.strip())
    if not bins or bins[0] != 1 or any(a >= b for a, b in zip(bins, bins[1:])):
        raise ValueError("heights must increase strictly and start at 1")
    return bins


def run_depth(
    depth: int,
    heights: tuple[Fraction, ...],
    children: int,
    policy_name: str,
    iterations: int,
    denom_pow: int,
) -> None:
    transitions = build_correlated_height_transitions(
        depth, heights, children, include_shrinking=True
    )
    n = len(transitions)

    if policy_name.startswith("const"):
        digit = int(policy_name[len("const"):] or "1")
        policy = constant_policy(transitions, digit)
        pol_desc = f"const t={digit}"
    elif policy_name == "min":
        policy, mlo, mhi = minimizing_policy(transitions, iterations)
        pol_desc = f"min (nl ratio [{mlo:.9f},{mhi:.9f}])"
    else:
        raise ValueError(f"unknown policy {policy_name!r}")

    matrix = policy_matrix(transitions, policy)
    lo, hi, _ = spectral_bounds(matrix, iterations)
    numer, dp, worst, ok = build_left_dual(matrix, iterations, denom_pow)

    # residue-memory compression: how many of the ternary digits does the policy
    # actually depend on?  Constant policies depend on none.
    print(
        f"  depth={depth:2d} states={n:6d} children={children} floors={len(heights)}"
        f" policy={pol_desc}"
    )
    print(
        f"      spectral radius in [{lo:.9f}, {hi:.9f}]   "
        f"exact dual (denom 2^{dp}): {'VERIFIED <' if ok else 'FAILED'}"
        f"  worst slack={float(worst):.3e}"
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depths", default="6,7,8", help="comma-separated ternary depths")
    parser.add_argument(
        "--policy",
        default="const1",
        help="const0|const1|const2|min (fixed row-selection policy)",
    )
    parser.add_argument(
        "--children",
        type=int,
        default=7,
        help="number of reusable growing costs per state (default 7)",
    )
    parser.add_argument(
        "--heights",
        default=",".join(str(h) for h in CORRELATED_THREE_QUARTERS_HEIGHT_BINS),
        help="comma-separated height floors, e.g. 1,7/4,3,6,12,24",
    )
    parser.add_argument(
        "--memory",
        type=int,
        default=0,
        help="if >0, run the depth-uniform finite-memory supersolution at this "
        "residue memory (states mod 3^memory) instead of the per-depth duals",
    )
    parser.add_argument("--iterations", type=int, default=2000)
    parser.add_argument(
        "--denom-pow",
        type=int,
        default=40,
        help="common denominator 2^k for the exact integer dual verifier",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    depths = [int(v) for v in args.depths.split(",") if v.strip()]
    heights = parse_heights(args.heights)
    print("harmonic (alpha=1) dual obstruction — exact rational verifier")
    print(f"  heights={tuple(str(h) for h in heights)}  children={args.children}")

    if args.memory > 0:
        print(
            f"  depth-uniform finite-memory supersolution (constant lift 1), "
            f"memory mod 3^{args.memory}:"
        )
        nclasses, nstates, cf, cq, ok = finite_memory_supersolution(
            args.memory, heights, args.children, args.iterations, args.denom_pow
        )
        print(
            f"      classes={nclasses} check-states={nstates} (depth {args.memory + 1})"
        )
        print(
            f"      exact contraction c = {cf:.12f} = {cq}"
            f"   uniform bound at ALL depths k>={args.memory}: "
            f"{'PROVED c<1' if ok and cq < 1 else 'FAILED (c>=1)'}"
        )
        return

    for depth in depths:
        run_depth(
            depth,
            heights,
            args.children,
            args.policy,
            args.iterations,
            args.denom_pow,
        )


if __name__ == "__main__":
    main()
