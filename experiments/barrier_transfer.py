#!/usr/bin/env -S uv run --quiet python3
"""Search exact finite transfer certificates in the barriered inverse tree.

An odd inverse macro-child of ``x`` at cost ``j`` is

    y = (2^j x - 1) / 3,

whose forward block is ``y -> 2^j x -> ... -> x``.  For ``j >= 2`` and
``x >= 2`` the child is larger than its parent, so the whole block stays above
the parent's floor and has peak at most ``2^j x``.  We retain only children
that are units modulo 3, because those can branch again.

Integrality and unit status depend only on ``x mod 9``.  This script derives
the ordered cost stream in every unit residue class rather than assuming a
table, takes the coordinatewise worst stream, and searches for a finite exact
weighted certificate

    sum(q^cost) > 1.

Such a certificate is the Collatz-specific input to a standard variable-length
tree-growth lemma.  With ``q = 5/6``, it gives growth on the scale
``q^-p = (6/5)^p`` inside the ceiling ``2^p x``.  The script also computes
prefix-free finite-budget leaf counts and exhaustively checks the arithmetic,
forward blocks, and cross-parent non-collision on a configurable finite range.

The second part implements the harder shrinking ``j = 1`` transfer.  It uses
residues modulo ``3^k`` and rational lower bounds for ``x/d``; loss of the next
ternary digit is handled adversarially.  A frozen 36-state integer potential
(modulo 27, height floors ``1`` and ``7/4``) is checked in exact arithmetic at
``q = 7/9``.  The optional nonlinear search explains where that certificate
came from, but is explicitly diagnostic rather than part of the exact check.

Examples:
    uv run --quiet python3 experiments/barrier_transfer.py
    uv run --quiet python3 experiments/barrier_transfer.py --verify-up-to 100000
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
from fractions import Fraction
from math import exp, log, log2


UNIT_RESIDUES_MOD_9 = (1, 2, 4, 5, 7, 8)

# Exact residue-plus-height certificate, in state order
#   height in (1, 7/4), then residue in UNITS_MOD_27.
# These small integer potentials were found numerically and are verified below
# using Fraction arithmetic.  They are data, not floating-point evidence.
UNITS_MOD_27 = tuple(value for value in range(27) if value % 3 != 0)
HEIGHT_CERTIFICATE_BINS = (Fraction(1), Fraction(7, 4))
HEIGHT_CERTIFICATE_Q = Fraction(7, 9)
HEIGHT_CERTIFICATE_WEIGHTS = (
    1278, 800, 1028, 972, 820, 588, 1117, 1045, 804,
    1055, 756, 638, 1254, 831, 965, 975, 758, 590,
    1356, 1648, 1028, 972, 820, 1325, 1249, 1619, 1069,
    1055, 756, 1245, 1254, 1441, 1344, 975, 758, 1036,
)


def step(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1


def odd_macro_child(x: int, cost: int) -> int | None:
    """Return the odd macro-child at ``cost``, or ``None`` if nonintegral."""
    numerator = 2**cost * x - 1
    return numerator // 3 if numerator % 3 == 0 else None


def is_reusable_growing_cost(residue: int, cost: int) -> bool:
    """Test a cost using only a representative of ``x mod 9``."""
    if cost < 2:
        return False
    child = odd_macro_child(residue, cost)
    return child is not None and child % 2 == 1 and child % 3 != 0


def first_reusable_costs(residue: int, count: int) -> tuple[int, ...]:
    costs: list[int] = []
    cost = 2
    while len(costs) < count:
        if is_reusable_growing_cost(residue, cost):
            costs.append(cost)
        cost += 1
    return tuple(costs)


def coordinatewise_envelope(rows: dict[int, tuple[int, ...]]) -> tuple[int, ...]:
    width = len(next(iter(rows.values())))
    assert all(len(row) == width for row in rows.values())
    return tuple(max(row[index] for row in rows.values()) for index in range(width))


def expected_envelope(index: int) -> int:
    """The periodic worst stream: 5, 7, 11, 13, 17, 19, ..."""
    block, offset = divmod(index, 2)
    return 6 * block + (5 if offset == 0 else 7)


def minimum_supercritical_prefix(
    costs: tuple[int, ...], q: Fraction
) -> tuple[tuple[int, ...], Fraction]:
    weight = Fraction(0)
    for index, cost in enumerate(costs):
        weight += q**cost
        if weight > 1:
            return costs[: index + 1], weight
    raise ValueError("cost prefix is too short to produce a supercritical certificate")


def critical_exponent() -> tuple[float, float]:
    """Solve q^5 + q^6 + q^7 = 1 for the infinite envelope."""
    low, high = 0.0, 1.0
    for _ in range(100):
        q = (low + high) / 2
        if q**5 + q**6 + q**7 < 1:
            low = q
        else:
            high = q
    q = (low + high) / 2
    return q, -log2(q)


def prefix_free_leaf_counts(costs: tuple[int, ...], max_budget: int) -> list[int]:
    """Best leaf count from recursively using every affordable child.

    A node may remain a leaf, or be replaced by the disjoint child subtrees
    whose certified costs fit in the remaining budget.  Because every term is
    positive, taking every affordable child maximizes the recurrence.
    """
    counts = [1]
    for budget in range(1, max_budget + 1):
        expanded = sum(counts[budget - cost] for cost in costs if cost <= budget)
        counts.append(max(1, expanded))
    return counts


def verify_forward_block(x: int, child: int, cost: int) -> None:
    value = child
    values = [value]
    for _ in range(cost + 1):
        value = step(value)
        values.append(value)
    assert value == x
    assert min(values) >= x
    assert max(values) == 2**cost * x


def verify_arithmetic(rows: dict[int, tuple[int, ...]], limit: int) -> int:
    owners: dict[int, int] = {}
    checked = 0
    width = len(next(iter(rows.values())))
    for x in range(2, limit + 1):
        if x % 3 == 0:
            continue
        costs = first_reusable_costs(x % 9, width)
        assert costs == rows[x % 9]
        children: list[int] = []
        for cost in costs:
            child = odd_macro_child(x, cost)
            assert child is not None
            assert child > x
            assert child % 2 == 1
            assert child % 3 != 0
            assert 3 * child + 1 == 2**cost * x
            verify_forward_block(x, child, cost)
            children.append(child)
            checked += 1
        assert len(set(children)) == width

        # The collision theorem used by iteration assumes distinct odd parents.
        if x % 2 == 1:
            for child in children:
                previous = owners.setdefault(child, x)
                assert previous == x
    return checked


def shrinking_child_class(residue: int) -> str:
    child = odd_macro_child(residue, 1)
    if child is None:
        return "nonintegral"
    return "unit" if child % 3 != 0 else "multiple-of-3"


def parse_fraction(value: str) -> Fraction:
    return Fraction(value.strip())


def child_residue_possibilities(residue: int, cost: int, ternary_depth: int) -> tuple[int, ...]:
    """Possible child residues after division loses one known ternary digit.

    If ``x`` is known modulo ``3^k``, then its odd macro-child is determined
    modulo ``3^(k-1)``.  The next base-3 digit is genuinely unknown, so a
    universal certificate must survive all three lifts modulo ``3^k``.
    """
    modulus = 3**ternary_depth
    lower_modulus = modulus // 3
    numerator = 2**cost * residue - 1
    assert numerator % 3 == 0
    base = (numerator // 3) % lower_modulus
    possibilities = tuple(base + digit * lower_modulus for digit in range(3))
    assert all(value % 3 != 0 for value in possibilities)
    return possibilities


def next_height_lower_bound(height: Fraction, cost: int) -> Fraction:
    """Uniform lower bound for y/d, using d >= 2.

    From x/d >= h and y = (2^j x - 1)/3,

        y/d >= (2^j h - 1/2)/3.
    """
    return (2**cost * height - Fraction(1, 2)) / 3


def build_height_transitions(
    ternary_depth: int,
    heights: tuple[Fraction, ...],
    growing_children: int,
    include_shrinking: bool,
) -> tuple[tuple[tuple[int, tuple[int, ...]], ...], ...]:
    if ternary_depth < 2:
        raise ValueError("the height-state search needs ternary depth at least 2")
    modulus = 3**ternary_depth
    residues = tuple(value for value in range(modulus) if value % 3 != 0)
    state_index = {
        (residue, height_index): height_index * len(residues) + residue_index
        for height_index in range(len(heights))
        for residue_index, residue in enumerate(residues)
    }

    transitions: list[tuple[tuple[int, tuple[int, ...]], ...]] = []
    for height_index, height in enumerate(heights):
        for residue in residues:
            costs = list(first_reusable_costs(residue % 9, growing_children))
            if include_shrinking and shrinking_child_class(residue % 9) == "unit":
                if next_height_lower_bound(height, 1) >= 1:
                    costs.insert(0, 1)

            edges: list[tuple[int, tuple[int, ...]]] = []
            for cost in costs:
                child_height = next_height_lower_bound(height, cost)
                if child_height < 1:
                    continue
                child_height_index = bisect_right(heights, child_height) - 1
                child_height_index = min(child_height_index, len(heights) - 1)
                targets = tuple(
                    state_index[(child_residue, child_height_index)]
                    for child_residue in child_residue_possibilities(
                        residue, cost, ternary_depth
                    )
                )
                edges.append((cost, targets))
            assert edges
            transitions.append(tuple(edges))
    return tuple(transitions)


def nonlinear_radius(
    transitions: tuple[tuple[tuple[int, tuple[int, ...]], ...], ...],
    q: float,
    iterations: int,
) -> tuple[float, float, int]:
    """Collatz bounds for the monotone min-over-lifts transfer operator."""
    weights = [1.0] * len(transitions)
    lower = upper = 0.0
    for iteration in range(1, iterations + 1):
        image = [
            sum(q**cost * min(weights[target] for target in targets)
                for cost, targets in edges)
            for edges in transitions
        ]
        ratios = [new / old for new, old in zip(image, weights)]
        lower, upper = min(ratios), max(ratios)

        # Normalize in log space, with damping for the nonsmooth min operator.
        scale = exp(sum(log(value) for value in image) / len(image))
        normalized = [value / scale for value in image]
        updated = [(old * new) ** 0.5 for old, new in zip(weights, normalized)]
        delta = max(abs(log(new / old)) for new, old in zip(updated, weights))
        weights = updated
        if delta < 1e-13 and upper - lower < 1e-11:
            return lower, upper, iteration
    return lower, upper, iterations


def search_height_critical_q(
    transitions: tuple[tuple[tuple[int, tuple[int, ...]], ...], ...],
    iterations: int,
) -> tuple[float, float, float, int]:
    low, high = 0.5, 0.999
    last_iterations = 0
    for _ in range(48):
        q = (low + high) / 2
        lower, upper, last_iterations = nonlinear_radius(transitions, q, iterations)
        estimate = (lower * upper) ** 0.5
        if estimate < 1:
            low = q
        else:
            high = q
    q = (low + high) / 2
    lower, upper, last_iterations = nonlinear_radius(transitions, q, iterations)
    return q, lower, upper, last_iterations


def verify_exact_height_certificate() -> tuple[Fraction, Fraction]:
    """Check all 36 weighted transfer inequalities in exact arithmetic."""
    transitions = build_height_transitions(
        ternary_depth=3,
        heights=HEIGHT_CERTIFICATE_BINS,
        growing_children=7,
        include_shrinking=True,
    )
    weights = HEIGHT_CERTIFICATE_WEIGHTS
    assert len(transitions) == len(weights) == 2 * len(UNITS_MOD_27)
    margins: list[Fraction] = []
    ratios: list[Fraction] = []
    for weight, edges in zip(weights, transitions):
        image = sum(
            HEIGHT_CERTIFICATE_Q**cost
            * min(weights[target] for target in targets)
            for cost, targets in edges
        )
        margins.append(image - weight)
        ratios.append(image / weight)
    assert min(margins) > 0
    assert min(ratios) > 1
    return min(margins), min(ratios)


def run_height_search(args: argparse.Namespace) -> None:
    heights = tuple(parse_fraction(value) for value in args.height_bins.split(",") if value)
    if not heights or heights[0] != 1 or any(a >= b for a, b in zip(heights, heights[1:])):
        raise ValueError("--height-bins must increase strictly and start at 1")

    print()
    print("height/residue transfer search (numerical candidate, not a proof)")
    print("  bins: " + ",".join(map(str, heights)))
    for include_shrinking in (False, True):
        transitions = build_height_transitions(
            args.ternary_depth, heights, args.height_children, include_shrinking
        )
        q, lower, upper, iterations = search_height_critical_q(
            transitions, args.height_iterations
        )
        label = "growing+j=1" if include_shrinking else "growing control"
        edge_count = sum(len(edges) for edges in transitions)
        print(
            f"  {label:15s}: states={len(transitions)}, edges={edge_count}, "
            f"q~{q:.12f}, exponent~{-log2(q):.12f}, "
            f"ratio=[{lower:.12f},{upper:.12f}], iterations={iterations}"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--children",
        type=int,
        default=12,
        help="number of reusable growing costs derived in each residue class",
    )
    parser.add_argument(
        "--verify-up-to",
        type=int,
        default=10_000,
        help="exhaustively check all unit parents through this value",
    )
    parser.add_argument(
        "--budgets",
        default="13,19,30,80",
        help="comma-separated bit budgets for prefix-free leaf counts",
    )
    parser.add_argument("--q-num", type=int, default=5)
    parser.add_argument("--q-den", type=int, default=6)
    parser.add_argument(
        "--height-search",
        action="store_true",
        help="run the conservative residue-plus-height j=1 transfer search",
    )
    parser.add_argument("--ternary-depth", type=int, default=3)
    parser.add_argument("--height-children", type=int, default=7)
    parser.add_argument("--height-iterations", type=int, default=4000)
    parser.add_argument(
        "--height-bins",
        default="1,7/4",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.children < 1:
        raise ValueError("--children must be positive")
    if args.verify_up_to < 2:
        raise ValueError("--verify-up-to must be at least 2")
    q = Fraction(args.q_num, args.q_den)
    if not 0 < q < 1:
        raise ValueError("q must lie strictly between 0 and 1")

    rows = {
        residue: first_reusable_costs(residue, args.children)
        for residue in UNIT_RESIDUES_MOD_9
    }
    envelope = coordinatewise_envelope(rows)
    expected = tuple(expected_envelope(index) for index in range(args.children))
    assert envelope == expected

    print("growing reusable odd-child costs by parent residue mod 9")
    for residue, costs in rows.items():
        print(f"  {residue}: " + ",".join(map(str, costs)))
    print("worst: " + ",".join(map(str, envelope)))

    prefix, weight = minimum_supercritical_prefix(envelope, q)
    denominator = args.q_den ** prefix[-1]
    numerator = sum(
        args.q_num**cost
        * args.q_den ** (prefix[-1] - cost)
        for cost in prefix
    )
    assert weight == Fraction(numerator, denominator)
    assert numerator > denominator
    print()
    print(
        f"finite transfer: q={args.q_num}/{args.q_den}, costs={list(prefix)}, "
        f"sum(q^j)={float(weight):.12f} > 1"
    )
    print(
        f"exact margin: {numerator} - {denominator} = {numerator - denominator} "
        f"over {denominator}"
    )
    print(
        f"certified counting exponent: log2({args.q_den}/{args.q_num}) "
        f"= {log2(args.q_den / args.q_num):.12f}"
    )

    q_critical, exponent_critical = critical_exponent()
    print(
        f"infinite-envelope critical q={q_critical:.12f}; "
        f"limiting exponent={exponent_critical:.12f}"
    )

    budgets = sorted({int(value) for value in args.budgets.split(",") if value})
    if not budgets or budgets[0] < 0:
        raise ValueError("--budgets must contain nonnegative integers")
    counts = prefix_free_leaf_counts(prefix, budgets[-1])
    print()
    print("prefix-free leaves from the finite certificate")
    for budget in budgets:
        count = counts[budget]
        exponent = log2(count) / budget if budget else 0.0
        print(f"  p={budget:3d}: leaves={count:>10,d}, exponent={exponent:.12f}")

    checked = verify_arithmetic(rows, args.verify_up_to)
    print()
    print(
        f"verified {checked:,} child blocks for every 3-unit parent "
        f"2 <= x <= {args.verify_up_to:,}; odd-parent collisions: none"
    )

    print("j=1 child status by parent residue mod 9")
    for residue in UNIT_RESIDUES_MOD_9:
        print(f"  {residue}: {shrinking_child_class(residue)}")
    print("  safety condition when integral: (2*x - 1) / 3 >= d")

    margin, ratio = verify_exact_height_certificate()
    print()
    print("exact residue-plus-height certificate")
    print(
        "  states=36 (unit residues mod 27 x height floors {1,7/4}); "
        "growing children=7; shrinking j=1 enabled when certified safe"
    )
    print(
        f"  q=7/9; all rational inequalities strict; "
        f"minimum ratio={float(ratio):.12f}; minimum margin={float(margin):.12f}"
    )
    print(f"  transfer exponent: log2(9/7)={log2(9 / 7):.12f}")

    if args.height_search:
        run_height_search(args)


if __name__ == "__main__":
    main()
