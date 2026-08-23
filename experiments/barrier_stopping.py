#!/usr/bin/env -S uv run --quiet python3
"""First-exit stopping lines for the net-height barrier certificate.

The local 36-state certificate expands the exact telescoping mass

    sqrt(d / x) * potential(state(x)).

Starting at the low root ``d``, this script repeatedly expands every endpoint
``x <= H`` using the same seven growing children and optional safe ``j=1``
child as the Lean certificate.  Endpoints are frozen the first time they exceed
``H``.  A repeated value is reported rather than silently unfolded: in the
odd-parent tree it is the cycle alternative in the intended repeat-or-growth
theorem.

If no repeat occurs, every first-exit endpoint is at most ``2^23 H`` and every
complete Collatz block has peak at most ``2^25 H``.  The exact mass should
exceed the root potential, forcing more than

    potential(low,d) / 200 * sqrt(H/d)

distinct leaves.  This experiment validates the proposed stopping-line object;
the exact local inequalities themselves are already kernel-checked in Lean.

Examples:
    uv run --quiet python3 experiments/barrier_stopping.py
    uv run --quiet python3 experiments/barrier_stopping.py --seeds 5,7,11 --budgets 8,12,16
"""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from math import sqrt

from barrier_transfer import (
    NET_HALF_WEIGHTS,
    UNITS_MOD_27,
    first_reusable_costs,
    odd_macro_child,
)


MAX_GROWING_COST = 23
MAX_POTENTIAL = max(NET_HALF_WEIGHTS)
UNIT_INDEX_MOD_27 = {residue: index for index, residue in enumerate(UNITS_MOD_27)}


@dataclass(frozen=True)
class Node:
    value: int
    high: bool
    path: tuple[int, ...]


def potential(value: int, high: bool) -> int:
    offset = len(UNITS_MOD_27) if high else 0
    return NET_HALF_WEIGHTS[offset + UNIT_INDEX_MOD_27[value % 27]]


def certified_children(node: Node, floor: int) -> tuple[Node, ...]:
    costs = list(first_reusable_costs(node.value % 9, 7))
    if node.high and node.value % 9 in (2, 8):
        costs.append(1)

    children: list[Node] = []
    for cost in costs:
        child = odd_macro_child(node.value, cost)
        assert child is not None
        child_high = False if cost == 1 else node.high or cost >= 3
        assert child >= floor
        assert child % 2 == 1 and child % 3 != 0
        assert 3 * child + 1 == 2**cost * node.value
        children.append(Node(child, child_high, node.path + (child,)))
    assert len({child.value for child in children}) == len(children)
    return tuple(children)


def stopping_line(seed: int, budget: int) -> dict[str, float | int]:
    if seed < 2 or seed % 2 == 0 or seed % 3 == 0:
        raise ValueError("stopping-line seeds must be odd, at least 2, and units modulo 3")
    ceiling = seed * 2**budget
    root = Node(seed, False, (seed,))
    active = deque([root])
    seen: dict[int, tuple[int, ...]] = {seed: root.path}
    leaves: list[Node] = []
    internal_count = 0

    while active:
        parent = active.popleft()
        internal_count += 1
        for child in certified_children(parent, seed):
            previous = seen.get(child.value)
            if previous is not None:
                raise RuntimeError(
                    "repeat/collision found: "
                    f"value={child.value}, first_path={previous}, second_path={child.path}"
                )
            seen[child.value] = child.path
            if child.value > ceiling:
                leaves.append(child)
            else:
                active.append(child)

    root_potential = potential(seed, False)
    mass = sum(
        sqrt(seed / leaf.value) * potential(leaf.value, leaf.high)
        for leaf in leaves
    )
    scale = sqrt(ceiling / seed)
    certified_count_floor = root_potential / MAX_POTENTIAL * scale
    max_leaf = max(leaf.value for leaf in leaves)
    min_leaf = min(leaf.value for leaf in leaves)
    assert mass > root_potential
    assert len(leaves) > certified_count_floor
    assert max_leaf < 2**MAX_GROWING_COST * ceiling

    return {
        "budget": budget,
        "ceiling": ceiling,
        "internal": internal_count,
        "leaves": len(leaves),
        "mass_ratio": mass / root_potential,
        "count_over_sqrt": len(leaves) / scale,
        "certified_count_floor": certified_count_floor,
        "min_overshoot": min_leaf / ceiling,
        "max_overshoot": max_leaf / ceiling,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seeds", default="5,7,11,13,17,19,23,25")
    parser.add_argument("--budgets", default="6,9,12")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    seeds = [int(value) for value in args.seeds.split(",") if value]
    budgets = [int(value) for value in args.budgets.split(",") if value]
    for seed in seeds:
        print(f"seed={seed}, low potential={potential(seed, False)}")
        for budget in budgets:
            result = stopping_line(seed, budget)
            print(
                "  "
                f"p={result['budget']:2d}, H={result['ceiling']:,}, "
                f"internal={result['internal']:,}, leaves={result['leaves']:,}, "
                f"mass/root={result['mass_ratio']:.6f}, "
                f"leaves/sqrt(H/d)={result['count_over_sqrt']:.6f}, "
                f"cert-floor={result['certified_count_floor']:.3f}, "
                f"overshoot=[{result['min_overshoot']:.3f},{result['max_overshoot']:.3f}]"
            )


if __name__ == "__main__":
    main()
