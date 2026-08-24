#!/usr/bin/env -S uv run --quiet python3
"""Test whether two shared ternary digits improve the barrier transfer.

The one-generation operator in ``barrier_transfer.py`` remembers ``x mod 3^k``
and lets the next ternary digit choose the joint state of every child.  This
control retains *two* unknown source digits and expands every child once more
before forgetting them.  Thus the second-generation choices of different
children remain correlated; an adversary cannot choose a fresh digit for each
child independently.

For a source residue ``r mod 3^k``, the nine alternatives are the lifts

    r + t₀ 3^k + t₁ 3^(k+1),    t₀,t₁ in {0,1,2}.

Every macro leaf is computed by two exact odd inverse blocks.  Its weight at
endpoint exponent ``alpha`` is

    (3 / 2^j)^alpha (3 / 2^l)^alpha
      = 3^(2 alpha) 2^(-alpha (j+l)).

By default the exact rational lower bound for the intermediate endpoint height
is retained until the second block.  ``--round-intermediate-height`` instead
rounds immediately to the five-state floor, separating that small geometric
gain from the shared-digit gain.

This is a diagnostic, not a proof.  The observed depth-5 critical exponent is
about 0.764596, compared with 0.755567 for one generation at depth 5 and
0.772226 for one generation at depth 6.  Consequently the extra correlation
is real, but it does not outperform simply retaining one more residue digit.

Examples:
    uv run --quiet python3 experiments/barrier_two_step.py
    uv run --quiet python3 experiments/barrier_two_step.py --depths 6
    uv run --quiet python3 experiments/barrier_two_step.py --depths 5 \
      --round-intermediate-height
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
from fractions import Fraction
from math import exp, log

from barrier_transfer import (
    CORRELATED_FOUR_FIFTHS_HEIGHT_BINS,
    first_reusable_costs,
    next_height_lower_bound,
    shrinking_child_class,
)


Transition = tuple[int, int]
Alternative = tuple[Transition, ...]
TwoStepTransitions = tuple[tuple[Alternative, ...], ...]


def available_costs(residue: int, height: Fraction) -> tuple[int, ...]:
    """The seven growing costs, plus the floor-safe shrinking cost if present."""
    costs = list(first_reusable_costs(residue % 9, 7))
    if (
        shrinking_child_class(residue % 9) == "unit"
        and next_height_lower_bound(height, 1) >= 1
    ):
        costs.insert(0, 1)
    return tuple(costs)


def build_two_step_transitions(
    ternary_depth: int,
    heights: tuple[Fraction, ...] = CORRELATED_FOUR_FIFTHS_HEIGHT_BINS,
    *,
    retain_intermediate_height: bool = True,
) -> TwoStepTransitions:
    """Build the exact two-source-digit/two-generation macro operator."""
    if ternary_depth < 2:
        raise ValueError("ternary depth must be at least 2")
    if not heights or heights[0] != 1 or any(a >= b for a, b in zip(heights, heights[1:])):
        raise ValueError("height floors must increase strictly and start at 1")

    modulus = 3**ternary_depth
    residues = tuple(value for value in range(modulus) if value % 3 != 0)
    residue_index = {residue: index for index, residue in enumerate(residues)}
    residue_count = len(residues)

    def state_index(residue: int, height_index: int) -> int:
        return height_index * residue_count + residue_index[residue]

    transitions: list[tuple[Alternative, ...]] = []
    for source_height in heights:
        for source_residue in residues:
            first_costs = available_costs(source_residue, source_height)
            alternatives: list[Alternative] = []
            for two_digits in range(9):
                # This representative contains exactly the two source digits
                # needed to determine every grandchild modulo 3^k.
                lifted_source = source_residue + two_digits * modulus
                leaves: list[Transition] = []
                for first_cost in first_costs:
                    numerator = 2**first_cost * lifted_source - 1
                    assert numerator % 3 == 0
                    child = (numerator // 3) % (3 * modulus)
                    child_residue = child % modulus

                    exact_child_height = next_height_lower_bound(
                        source_height, first_cost
                    )
                    assert exact_child_height >= 1
                    child_height_index = bisect_right(heights, exact_child_height) - 1
                    child_height_index = min(child_height_index, len(heights) - 1)
                    second_source_height = (
                        exact_child_height
                        if retain_intermediate_height
                        else heights[child_height_index]
                    )

                    for second_cost in available_costs(
                        child_residue, second_source_height
                    ):
                        second_numerator = 2**second_cost * child - 1
                        assert second_numerator % 3 == 0
                        grandchild_residue = (second_numerator // 3) % modulus
                        grandchild_height = next_height_lower_bound(
                            second_source_height, second_cost
                        )
                        assert grandchild_height >= 1
                        grandchild_height_index = (
                            bisect_right(heights, grandchild_height) - 1
                        )
                        grandchild_height_index = min(
                            grandchild_height_index, len(heights) - 1
                        )
                        leaves.append(
                            (
                                first_cost + second_cost,
                                state_index(
                                    grandchild_residue, grandchild_height_index
                                ),
                            )
                        )
                assert leaves
                alternatives.append(tuple(leaves))
            assert len(alternatives) == 9
            transitions.append(tuple(alternatives))
    return tuple(transitions)


def two_step_nonlinear_eigenvector(
    transitions: TwoStepTransitions,
    exponent: float,
    iterations: int,
    initial: tuple[float, ...] | None = None,
) -> tuple[float, float, int, tuple[float, ...]]:
    """Collatz bounds for the min-of-nine two-generation operator."""
    weights = [1.0] * len(transitions) if initial is None else list(initial)
    max_cost = max(
        cost
        for alternatives in transitions
        for leaves in alternatives
        for cost, _ in leaves
    )
    coefficients = tuple(
        3.0 ** (2.0 * exponent) * 2.0 ** (-exponent * cost)
        for cost in range(max_cost + 1)
    )
    lower = upper = 0.0
    for iteration in range(1, iterations + 1):
        image = [
            min(
                sum(coefficients[cost] * weights[target] for cost, target in leaves)
                for leaves in alternatives
            )
            for alternatives in transitions
        ]
        ratios = [new / old for new, old in zip(image, weights)]
        lower, upper = min(ratios), max(ratios)

        scale = exp(sum(log(value) for value in image) / len(image))
        normalized = [value / scale for value in image]
        updated = [(old * new) ** 0.5 for old, new in zip(weights, normalized)]
        delta = max(abs(log(new / old)) for new, old in zip(updated, weights))
        weights = updated
        if delta < 1e-13 and upper - lower < 1e-11:
            break
    return lower, upper, iteration, tuple(weights)


def search_two_step_critical_exponent(
    transitions: TwoStepTransitions,
    iterations: int,
) -> tuple[float, float, float, int]:
    """Numerically solve rho(T₂(alpha)) = 1."""
    low, high = 0.0, 1.5
    weights: tuple[float, ...] | None = None
    for _ in range(42):
        exponent = (low + high) / 2
        lower, upper, _, weights = two_step_nonlinear_eigenvector(
            transitions, exponent, iterations, weights
        )
        estimate = (lower * upper) ** 0.5
        if estimate > 1:
            low = exponent
        else:
            high = exponent
    exponent = (low + high) / 2
    lower, upper, used_iterations, _ = two_step_nonlinear_eigenvector(
        transitions, exponent, iterations, weights
    )
    return exponent, lower, upper, used_iterations


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--depths",
        default="2,3,4,5",
        help="comma-separated ternary depths (depth 7 takes several minutes)",
    )
    parser.add_argument("--iterations", type=int, default=600)
    parser.add_argument(
        "--round-intermediate-height",
        action="store_true",
        help="round the child height before its second expansion",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    depths = [int(value) for value in args.depths.split(",") if value]
    if not depths or min(depths) < 2:
        raise ValueError("--depths must contain integers at least 2")
    if args.iterations < 1:
        raise ValueError("--iterations must be positive")

    mode = "rounded" if args.round_intermediate_height else "retained exact lower bound"
    print("two-generation shared-lift transfer (numerical diagnostic)")
    print(f"  intermediate height: {mode}")
    for depth in depths:
        transitions = build_two_step_transitions(
            depth,
            retain_intermediate_height=not args.round_intermediate_height,
        )
        leaf_entries = sum(
            len(leaves) for alternatives in transitions for leaves in alternatives
        )
        exponent, lower, upper, iterations = search_two_step_critical_exponent(
            transitions, args.iterations
        )
        print(
            f"  depth={depth}: states={len(transitions)}, alternatives=9, "
            f"leaf_entries={leaf_entries}, exponent~{exponent:.12f}, "
            f"ratio=[{lower:.12f},{upper:.12f}], iterations={iterations}"
        )


if __name__ == "__main__":
    main()
