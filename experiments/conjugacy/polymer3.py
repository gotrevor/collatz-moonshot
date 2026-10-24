#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
The fair null for the Collatz environment w(n, m) = e(-<x_{m+1}>_{n+2}), x_t = xi 3^{-t}:
keep the truncation structure (the phases of one x_t at successive levels are nested
truncations of one 2-adic number) but make the x_t independent uniform 2-adic integers.
Compares slopes of log2|G_n| on [N/2, N] (polymer2.slope) for: Collatz panel (independent
environments only: xi = 1, 5, 7, 5/7, rand64), random-2-adic null, iid-phase null.
Usage: polymer3.py N SEEDS
"""
import random
import sys

import numpy as np

from polymer import collatz_weights, iid_weights, run
from polymer2 import slope


def random2adic_weights(seed: int, N: int):
    rng = random.Random(seed)
    J = N + 3
    f = [rng.getrandbits(J) for _ in range(N + 2)]

    def w(n, size):
        q = 1 << (n + 2)
        ang = np.array([((f[m] % q) << 53) // q for m in range(size)], dtype=np.float64) / 2.0 ** 53
        return np.exp(-2j * np.pi * ang)
    return w


def summary(name, xs):
    xs = np.array(xs)
    print(f"{name:>14}: mean {xs.mean():.5f}  sd {xs.std(ddof=1):.5f}  n={len(xs)}  "
          f"[{xs.min():.5f}, {xs.max():.5f}]", flush=True)
    return xs


def main() -> int:
    N, seeds = int(sys.argv[1]), int(sys.argv[2])
    mod = 1 << (N + 3)
    rnd = random.Random(20261024).getrandbits(64) | 1
    panel = [1, 5, 7, 5 * pow(7, -1, mod) % mod, rnd]
    c = summary("collatz", [slope(run(collatz_weights(xi, N), N), N) for xi in panel])
    r = summary("random 2-adic", [slope(run(random2adic_weights(500 + s, N), N), N) for s in range(seeds)])
    i = summary("iid phases", [slope(run(iid_weights(100 + s), N), N) for s in range(seeds)])
    for name, other in [("random 2-adic", r), ("iid phases", i)]:
        se = (c.var(ddof=1) / len(c) + other.var(ddof=1) / len(other)) ** 0.5
        print(f"collatz - {name}: {c.mean() - other.mean():+.5f}  (Welch z = {(c.mean() - other.mean()) / se:+.1f})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
