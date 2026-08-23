#!/usr/bin/env -S uv run --quiet python3
"""Census the floor-preserving backward Collatz tree (Front A, Route A2).

For a seed d and a ceiling X = 2^p d, define the finite barriered tree

    B_d(p) = {m : some forward path m -> ... -> d stays in [d, X]}.

The ceiling removes an otherwise important ambiguity: an endpoint m <= X can
reach d through a much larger intermediate value.  As p grows, these finite
trees monotonically exhaust the full backward basin whose path never dips below
d.

For the unaccelerated map the inverse branches of x are

    2x                         (always),
    (x - 1) / 3               (exactly when x == 4 mod 6).

We measure harmonic mass because Tao's theorem uses logarithmic density.  The
dimensionless quantity

    d * sum_{m in B_d(p)} 1/m

has a universal doubling-spine contribution 2 - 2^-p.  The main diagnostic is
the excess above that spine, divided by log(2^p).  A positive stable value would
be the kind of logarithmic-mass growth a saturation theorem could try to use;
decay toward zero would be evidence against this naive tree observable.

The same traversal also records the raw backward basin (endpoints m >= d whose
path may dip below d), giving a direct safe/raw comparison.  Seeds are kept
separate by residue class: if 3 divides d, the exact backward tree is only the
doubling spine.

Examples:
    uv run --quiet python3 experiments/barrier_tree.py
    uv run --quiet python3 experiments/barrier_tree.py --seed-count 12 --powers 6,9,12,15
"""

from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from math import log
from statistics import median


@dataclass(frozen=True)
class Metrics:
    nodes: int
    scaled_mass: float
    odd_edges: int
    max_depth: int


@dataclass(frozen=True)
class SeedResult:
    seed: int
    powers: tuple[int, ...]
    safe: tuple[Metrics, ...]
    raw: tuple[Metrics, ...] | None
    visited: int
    repeated_edges: int


def barrier_bin(seed: int, peak: int) -> int:
    """Smallest p such that peak <= seed * 2^p, using integer arithmetic."""
    ratio_ceiling = (peak + seed - 1) // seed
    return (ratio_ceiling - 1).bit_length()


def inverse_children(x: int) -> tuple[tuple[int, bool], ...]:
    """Return (predecessor, used_odd_inverse) pairs for the ordinary Collatz map."""
    even_predecessor = 2 * x
    if x % 6 == 4:
        return ((even_predecessor, False), ((x - 1) // 3, True))
    return ((even_predecessor, False),)


def census_seed(
    seed: int, powers: tuple[int, ...], max_nodes: int, include_raw: bool = True
) -> SeedResult:
    if seed < 5:
        raise ValueError("use seeds >= 5, away from the 1-2-4 cycle")
    if not powers or powers[0] < 0 or any(a >= b for a, b in zip(powers, powers[1:])):
        raise ValueError("powers must be a strictly increasing list of nonnegative integers")

    max_power = powers[-1]
    ceiling = seed * 2**max_power

    # Exact-bin accumulators.  Taking prefix sums below yields every requested
    # ceiling from one traversal, because the forward path from a predecessor to
    # the root is unique.
    safe_count = [0] * (max_power + 1)
    raw_count = [0] * (max_power + 1)
    safe_mass = [0.0] * (max_power + 1)
    raw_mass = [0.0] * (max_power + 1)
    safe_odd = [0] * (max_power + 1)
    raw_odd = [0] * (max_power + 1)
    safe_depth = [0] * (max_power + 1)
    raw_depth = [0] * (max_power + 1)

    # Queue state is (node, reverse depth, path peak, path minimum, incoming edge odd?).
    traversal_floor = 1 if include_raw else seed
    queue = deque([(seed, 0, seed, seed, False)])
    seen = {seed}
    repeated_edges = 0

    while queue:
        x, depth, peak, low, incoming_odd = queue.popleft()

        if x >= seed:
            pbin = barrier_bin(seed, peak)
            raw_count[pbin] += 1
            raw_mass[pbin] += seed / x
            raw_odd[pbin] += int(incoming_odd)
            raw_depth[pbin] = max(raw_depth[pbin], depth)
            if low >= seed:
                safe_count[pbin] += 1
                safe_mass[pbin] += seed / x
                safe_odd[pbin] += int(incoming_odd)
                safe_depth[pbin] = max(safe_depth[pbin], depth)

        for child, is_odd in inverse_children(x):
            if child < traversal_floor or child > ceiling:
                continue
            if child in seen:
                repeated_edges += 1
                continue
            seen.add(child)
            if len(seen) > max_nodes:
                raise RuntimeError(
                    f"seed {seed}: exceeded --max-nodes={max_nodes:,} at ceiling 2^{max_power} d"
                )
            queue.append(
                (child, depth + 1, max(peak, child), min(low, child), is_odd)
            )

    def cumulative_metrics(
        counts: list[int], masses: list[float], odds: list[int], depths: list[int]
    ) -> tuple[Metrics, ...]:
        out: list[Metrics] = []
        count = odd = max_depth = 0
        mass = 0.0
        wanted = iter(enumerate(powers))
        wanted_index, wanted_power = next(wanted)
        for p in range(max_power + 1):
            count += counts[p]
            mass += masses[p]
            odd += odds[p]
            max_depth = max(max_depth, depths[p])
            if p == wanted_power:
                assert wanted_index == len(out)
                out.append(Metrics(count, mass, odd, max_depth))
                try:
                    wanted_index, wanted_power = next(wanted)
                except StopIteration:
                    break
        return tuple(out)

    return SeedResult(
        seed=seed,
        powers=powers,
        safe=cumulative_metrics(safe_count, safe_mass, safe_odd, safe_depth),
        raw=(
            cumulative_metrics(raw_count, raw_mass, raw_odd, raw_depth)
            if include_raw
            else None
        ),
        visited=len(seen),
        repeated_edges=repeated_edges,
    )


def spine_mass(power: int) -> float:
    return 2.0 - 2.0 ** (-power)


def normalized_excess(result: SeedResult, index: int) -> float:
    p = result.powers[index]
    if p == 0:
        return 0.0
    return (result.safe[index].scaled_mass - spine_mass(p)) / (p * log(2.0))


def safe_share(result: SeedResult, index: int) -> float:
    if result.raw is None:
        return float("nan")
    raw = result.raw[index].scaled_mass
    return result.safe[index].scaled_mass / raw if raw else 1.0


def median_or_nan(values: list[float]) -> float:
    return median(values) if values else float("nan")


def percentile(values: list[float], q: float) -> float:
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    position = q * (len(ordered) - 1)
    lower = int(position)
    fraction = position - lower
    return ordered[lower] * (1.0 - fraction) + ordered[lower + 1] * fraction


def print_summary(results: list[SeedResult], summary_only: bool) -> None:
    powers = results[0].powers
    has_raw = results[0].raw is not None
    print("inverse-branch sanity: even predecessor 2x; odd predecessor (x-1)/3 iff x = 4 mod 6")
    print("mass convention: scaled = d * sum(1/m); rate = (scaled - doubling spine) / log(2^p)")
    print()

    print("aggregate by seed mod 3")
    print(
        f"{'p':>3} {'class':>7} {'seeds':>5} {'med safe nodes':>14} "
        f"{'med scaled':>11} {'med rate':>10}"
        + (f" {'med safe/raw':>13}" if has_raw else "")
    )
    for index, p in enumerate(powers):
        for residue in range(3):
            group = [r for r in results if r.seed % 3 == residue]
            nodes = [float(r.safe[index].nodes) for r in group]
            masses = [r.safe[index].scaled_mass for r in group]
            rates = [normalized_excess(r, index) for r in group]
            line = (
                f"{p:3d} {('d=' + str(residue) + ' mod3'):>7} {len(group):5d} "
                f"{median_or_nan(nodes):14.1f} {median_or_nan(masses):11.6f} "
                f"{median_or_nan(rates):10.6f}"
            )
            if has_raw:
                shares = [safe_share(r, index) for r in group]
                line += f" {median_or_nan(shares):13.6f}"
            print(line)
        print()

    nonmultiples = [r for r in results if r.seed % 3]
    print("nonmultiple-of-3 rate distribution")
    print(f"{'p':>3} {'min':>10} {'q10':>10} {'median':>10} {'q90':>10} {'max':>10}")
    for index, p in enumerate(powers):
        rates = [normalized_excess(r, index) for r in nonmultiples]
        print(
            f"{p:3d} {min(rates):10.6f} {percentile(rates, 0.1):10.6f} "
            f"{median(rates):10.6f} {percentile(rates, 0.9):10.6f} {max(rates):10.6f}"
        )

    index = len(powers) - 1
    p = powers[index]
    if not summary_only:
        print()
        print(f"seed detail at largest ceiling p={p}")
        print(
            f"{'d':>7} {'mod18':>5} {'safe':>9}"
            + (f" {'raw':>9}" if has_raw else "")
            + f" {'odd':>7} {'depth':>6} {'scaled':>10} {'rate':>10}"
            + (f" {'safe/raw':>10}" if has_raw else "")
            + f" {'visited':>10}"
        )
        for r in results:
            s = r.safe[index]
            line = f"{r.seed:7d} {r.seed % 18:5d} {s.nodes:9d}"
            if has_raw:
                assert r.raw is not None
                line += f" {r.raw[index].nodes:9d}"
            line += (
                f" {s.odd_edges:7d} {s.max_depth:6d} {s.scaled_mass:10.6f} "
                f"{normalized_excess(r, index):10.6f}"
            )
            if has_raw:
                line += f" {safe_share(r, index):10.6f}"
            line += f" {r.visited:10d}"
            print(line)

    if nonmultiples:
        print()
        qualifier = "medians; multiples of 3 omitted as exact spine-only cases"
        print(f"residue detail at p={p} ({qualifier})")
        print(
            f"{'mod18':>5} {'n':>3} {'rate':>10}"
            + (f" {'safe/raw':>10}" if has_raw else "")
            + f" {'safe nodes':>12}"
        )
        for residue in range(18):
            group = [r for r in nonmultiples if r.seed % 18 == residue]
            if not group:
                continue
            line = (
                f"{residue:5d} {len(group):3d} "
                f"{median(normalized_excess(r, index) for r in group):10.6f}"
            )
            if has_raw:
                line += f" {median(safe_share(r, index) for r in group):10.6f}"
            line += f" {median(r.safe[index].nodes for r in group):12.1f}"
            print(line)

    repeats = sum(r.repeated_edges for r in results)
    print()
    print(f"duplicate/cycle edges skipped: {repeats}")
    divisible = [r for r in results if r.seed % 3 == 0]
    spine_ok = all(
        r.safe[i].nodes == p + 1
        and r.safe[i].odd_edges == 0
        and abs(r.safe[i].scaled_mass - spine_mass(p)) < 1e-12
        for r in divisible
        for i, p in enumerate(powers)
    )
    print(f"3|d exact-spine control: {'OK' if spine_ok else 'FAILED'}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed-start", type=int, default=10_000)
    parser.add_argument("--seed-count", type=int, default=36)
    parser.add_argument(
        "--powers",
        default="6,9,12,15",
        help="strictly increasing p values for ceilings 2^p d",
    )
    parser.add_argument(
        "--max-nodes",
        type=int,
        default=3_000_000,
        help="per-seed safety limit for the largest raw tree",
    )
    parser.add_argument(
        "--no-raw",
        action="store_true",
        help="enumerate only the barriered tree (faster and much less memory)",
    )
    parser.add_argument(
        "--summary-only",
        action="store_true",
        help="omit the one-line row for every individual seed",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    powers = tuple(int(x) for x in args.powers.split(",") if x)
    seeds = list(range(args.seed_start, args.seed_start + args.seed_count))
    results = [
        census_seed(seed, powers, args.max_nodes, include_raw=not args.no_raw)
        for seed in seeds
    ]
    print_summary(results, args.summary_only)


if __name__ == "__main__":
    main()
