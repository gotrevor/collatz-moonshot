#!/usr/bin/env -S uv run --quiet python3
"""Freeze and integer-verify the depth-uniform harmonic obstruction certificate.

The constant-lift-1 harmonic operator ``M_k`` (see ``barrier_harmonic_dual.py``)
admits a *depth-independent* supersolution: a positive weight ``w`` on the
classes ``(r mod 3^9, floor)`` such that the pullback obeys ``M_k w < w``
pointwise at **every** ternary depth ``k >= 9``.  The reason it is depth-uniform:

  * the harmonic edge coefficient ``3 / 2^cost`` depends only on ``r mod 9`` and
    the floor (via the reusable-cost set), and
  * under the fixed lift digit each child's residue mod ``3^9`` is determined by
    the source residue mod ``3^10``,

so the defining inequality for any depth-``k`` state is *identical* to one of the
finitely many inequalities at the mod-``3^10`` resolution (196 830 of them).

This module scales the weight to integers over ``2^WEIGHT_POW`` and checks every
inequality in **pure integer arithmetic** — exactly the shape a Lean
``native_decide`` will verify:

    sum_cost  3 * 2^(COST_MAX - cost) * W[child_class]   <   2^COST_MAX * W[source_class].

It emits the frozen ``Array Nat`` literal for the Lean module and prints the
exact contraction constant.  Run:

    uv run --quiet python3 experiments/harmonic_uniform_certificate.py
    uv run --quiet python3 experiments/harmonic_uniform_certificate.py --emit weights.txt
"""

from __future__ import annotations

import argparse
from fractions import Fraction

from barrier_transfer import (
    build_correlated_height_transitions,
    CORRELATED_THREE_QUARTERS_HEIGHT_BINS,
)

MEMORY = 9              # residue memory: classes use r mod 3^9
DEPTH = MEMORY + 1      # build/verify at mod 3^10 resolution
CHILDREN = 7
WEIGHT_POW = 30         # weights are integers over 2^WEIGHT_POW
POWER_ITERS = 4000


def build() -> tuple[list[int], int, int, Fraction, int]:
    heights = CORRELATED_THREE_QUARTERS_HEIGHT_BINS
    transitions = build_correlated_height_transitions(
        DEPTH, heights, CHILDREN, include_shrinking=True
    )
    modulus = 3**DEPTH
    units = [v for v in range(modulus) if v % 3 != 0]
    ucount = len(units)
    lowmod = 3**MEMORY
    lunits = [v for v in range(lowmod) if v % 3 != 0]
    lidx = {u: i for i, u in enumerate(lunits)}
    nclasses = len(lunits) * len(heights)

    def class_of(state: int) -> int:
        return (state // ucount) * len(lunits) + lidx[units[state % ucount] % lowmod]

    # const-lift-1 harmonic rows collapsed to class targets (float, for the solve)
    frows: list[tuple[int, list[tuple[int, float]]]] = []
    cost_max = 0
    for s in range(len(transitions)):
        acc: dict[int, float] = {}
        for cost, target in transitions[s][1]:
            cost_max = max(cost_max, cost)
            tc = class_of(target)
            acc[tc] = acc.get(tc, 0.0) + 3.0 / 2.0**cost
        frows.append((class_of(s), list(acc.items())))

    w = [1.0] * nclasses
    for _ in range(POWER_ITERS):
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

    denom = 2**WEIGHT_POW
    weights = [max(1, round(x * denom)) for x in w]

    # Pure-integer verification, exactly the Lean native_decide shape.
    worst_ratio = Fraction(0)
    violations = 0
    scale = 2**cost_max
    for s in range(len(transitions)):
        acc_i: dict[int, int] = {}
        for cost, target in transitions[s][1]:
            tc = class_of(target)
            acc_i[tc] = acc_i.get(tc, 0) + 3 * 2 ** (cost_max - cost) * weights[tc]
        lhs = sum(acc_i.values())          # == 2^cost_max * (M w)(s) * denom
        rhs = scale * weights[class_of(s)]  # == 2^cost_max * w(class) * denom
        if lhs >= rhs:
            violations += 1
        ratio = Fraction(lhs, rhs)
        if ratio > worst_ratio:
            worst_ratio = ratio
    return weights, nclasses, len(transitions), worst_ratio, cost_max, violations


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit", default="", help="write the Lean Array literal here")
    args = parser.parse_args()

    weights, nclasses, nstates, worst, cost_max, violations = build()
    print("depth-uniform harmonic obstruction certificate (constant lift 1)")
    print(f"  memory=mod 3^{MEMORY}  classes={nclasses}  check-states={nstates}")
    print(f"  weight scale=2^{WEIGHT_POW}  cost_max={cost_max}")
    print(f"  integer-verified violations: {violations} of {nstates}")
    print(f"  exact contraction c = {float(worst):.12f} = {worst}")
    print(f"  uniform bound at ALL depths k>={MEMORY}: "
          f"{'PROVED c<1' if violations == 0 and worst < 1 else 'FAILED'}")

    if args.emit:
        with open(args.emit, "w") as fh:
            fh.write(f"-- {nclasses} weights over 2^{WEIGHT_POW}, cost_max={cost_max}\n")
            fh.write("#[\n")
            for i in range(0, len(weights), 9):
                fh.write(", ".join(map(str, weights[i:i + 9])) + ",\n")
            fh.write("]\n")
        print(f"  emitted Lean literal -> {args.emit}")


if __name__ == "__main__":
    main()
