#!/usr/bin/env -S uv run --quiet python3
"""Stress-test uniform barrier-tree growth with nested 3-adic seed prefixes.

The first consecutive-seed census suggested a normalized harmonic slope around
0.2 or larger.  That is not a uniform lower bound: the integrality pattern of
odd inverse branches is controlled by progressively deeper base-3 digits of the
seed.  A deterministic random/prefix search found the curated seeds below.  The
last three share increasingly long low 3-adic prefixes and push the observed
slope downward as the ceiling deepens.

All curated seeds are below the repo's assumed verified convergence frontier,
so they are not on a nontrivial cycle.  This lets the deep mode traverse the
reverse arborescence without a memory-heavy visited set.

Examples:
    uv run --quiet python3 experiments/barrier_adversary.py
    uv run --quiet python3 experiments/barrier_adversary.py --deep-power 30
"""

from __future__ import annotations

import argparse
from math import log


CURATED_SEEDS = (
    1_000_052,
    359_421_848_168_309,
    798_338_741_946_713,
    10_205_741_556_338_552,
)


def step(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1


def verify_reaches_one(seed: int) -> None:
    seen: set[int] = set()
    value = seed
    while value != 1 and value not in seen:
        seen.add(value)
        value = step(value)
    if value != 1:
        raise RuntimeError(f"seed {seed} was not verified to reach 1")


def safe_metrics(seed: int, power: int) -> tuple[int, float, float]:
    """Depth-first exact traversal, valid after `verify_reaches_one(seed)`."""
    ceiling = seed * 2**power
    stack = [seed]
    nodes = 0
    scaled_mass = 0.0
    while stack:
        x = stack.pop()
        nodes += 1
        scaled_mass += seed / x
        even_predecessor = 2 * x
        if even_predecessor <= ceiling:
            stack.append(even_predecessor)
        if x % 6 == 4:
            odd_predecessor = (x - 1) // 3
            if odd_predecessor >= seed:
                stack.append(odd_predecessor)
    spine = 2.0 - 2.0 ** (-power)
    rate = (scaled_mass - spine) / (power * log(2.0))
    return nodes, scaled_mass, rate


def low_ternary_digits(seed: int, count: int) -> str:
    digits: list[str] = []
    value = seed
    for _ in range(count):
        digits.append(str(value % 3))
        value //= 3
    return "".join(digits)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--powers", default="15,18,21,24")
    parser.add_argument(
        "--deep-power",
        type=int,
        default=0,
        help="also run this ceiling on the final adversarial seed (30 visits ~52M nodes)",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    powers = [int(value) for value in args.powers.split(",") if value]
    print("seed low-ternary-digits " + " ".join(f"c(p={p})" for p in powers))
    for seed in CURATED_SEEDS:
        verify_reaches_one(seed)
        rates = [safe_metrics(seed, power)[2] for power in powers]
        print(
            f"{seed:>18} {low_ternary_digits(seed, 17)} "
            + " ".join(f"{rate:.9f}" for rate in rates)
        )

    if args.deep_power:
        seed = CURATED_SEEDS[-1]
        nodes, mass, rate = safe_metrics(seed, args.deep_power)
        print()
        print(
            f"deep seed={seed} p={args.deep_power} nodes={nodes:,} "
            f"scaled_mass={mass:.9f} rate={rate:.9f}"
        )


if __name__ == "__main__":
    main()
