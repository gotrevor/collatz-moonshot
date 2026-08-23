#!/usr/bin/env -S uv run --quiet python3
"""Can barrier-tree mass aggregate along a rising Collatz tail?

There is no known divergent orbit to sample.  As a finite proxy, take an
ordinary orbit only up to its global peak and retain its *future-minimum
records*: points d whose remaining path to that peak stays at least d.  These
are exactly the finite analogue of high-floor tail seeds supplied by a
hypothetical orbit tending to infinity.

For every record d, `barrier_tree.py` estimates the dimensionless coefficient

    c_d(p) = (d * harmonic_mass(B_d(p)) - doubling_spine) / log(2^p).

Undoing the scale costs 1/d.  This script measures the naive moving-tail budget
sum c_d(p)/d.  It ignores overlap, so it is an optimistic upper diagnostic for
any argument that simply adds the individual trees; rapid decay is therefore a
real warning, while non-decay would only justify a more careful union census.

Examples:
    uv run --quiet python3 experiments/barrier_tail.py
    uv run --quiet python3 experiments/barrier_tail.py --starts 27 --power 18 --detail
"""

from __future__ import annotations

import argparse

from barrier_tree import census_seed, normalized_excess


def step(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1


def orbit_to_one(start: int, limit: int) -> list[int]:
    orbit = [start]
    while orbit[-1] != 1 and len(orbit) <= limit:
        orbit.append(step(orbit[-1]))
    if orbit[-1] != 1:
        raise RuntimeError(f"start {start} did not reach 1 within --orbit-limit={limit}")
    return orbit


def future_minimum_records(values: list[int]) -> list[tuple[int, int]]:
    """Return (index, value) pairs that are strict minima of their finite suffix."""
    low: int | None = None
    records: list[tuple[int, int]] = []
    for index in range(len(values) - 1, -1, -1):
        value = values[index]
        if low is None or value < low:
            low = value
            records.append((index, value))
    records.reverse()
    return records


def tail_sums(values: list[float]) -> list[float]:
    out = [0.0] * len(values)
    total = 0.0
    for index in range(len(values) - 1, -1, -1):
        total += values[index]
        out[index] = total
    return out


def probe(start: int, power: int, max_nodes: int, orbit_limit: int, detail: bool) -> None:
    orbit = orbit_to_one(start, orbit_limit)
    peak_index = max(range(len(orbit)), key=orbit.__getitem__)
    segment = orbit[: peak_index + 1]
    # Multiples of 3 have only the doubling spine, hence zero excess coefficient.
    records = [(index, d) for index, d in future_minimum_records(segment) if d % 3]

    rows: list[tuple[int, int, float, float]] = []
    for index, d in records:
        result = census_seed(d, (power,), max_nodes, include_raw=False)
        coefficient = normalized_excess(result, 0)
        rows.append((index, d, coefficient, coefficient / d))

    budgets = [row[3] for row in rows]
    remaining = tail_sums(budgets)
    print(
        f"start={start} peak={orbit[peak_index]} peak_index={peak_index} "
        f"unit_records={len(rows)} p={power}"
    )
    print(f"  naive total sum(c_d/d) = {remaining[0]:.9g}")
    print(f"  start * total          = {start * remaining[0]:.9g}")
    print("  remaining tail budget:")
    sample_indices = sorted({0, len(rows) // 4, len(rows) // 2, 3 * len(rows) // 4, len(rows) - 1})
    for row_index in sample_indices:
        _, d, _, _ = rows[row_index]
        print(
            f"    record {row_index + 1:>3}/{len(rows):<3}  floor={d:<12} "
            f"sum={remaining[row_index]:.9g}"
        )

    if detail:
        print("  orbit_index floor c_d c_d/d tail_sum")
        for row_index, (orbit_index, d, coefficient, budget) in enumerate(rows):
            print(
                f"  {orbit_index:11d} {d:12d} {coefficient:10.6f} "
                f"{budget:12.6g} {remaining[row_index]:12.6g}"
            )
    print()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--starts", default="27,77031,837799")
    parser.add_argument("--power", type=int, default=15)
    parser.add_argument("--max-nodes", type=int, default=3_000_000)
    parser.add_argument("--orbit-limit", type=int, default=100_000)
    parser.add_argument("--detail", action="store_true")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    starts = [int(value) for value in args.starts.split(",") if value]
    for start in starts:
        probe(start, args.power, args.max_nodes, args.orbit_limit, args.detail)


if __name__ == "__main__":
    main()
