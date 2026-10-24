#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
Where does the extra cancellation live?  Block nulls interpolating null B (L = 1, independent
2-adic x_t) and the Collatz environment (L = inf, x_t = xi 3^{-t} with random 2-adic xi):
within each block of L consecutive powers keep x_t = 3 x_{t+1}; draw an independent uniform
2-adic integer for each block.  Slope of log2|G_n| on [N/2, N] (polymer2.slope).
Known answers (polymer4.py, N = 1600): L = 1 -> -0.513, L = inf -> -0.525.
Usage: polymer5.py N SEEDS L1 L2 ...   (L = 0 means inf)
"""
import random
import sys

import numpy as np

from polymer import collatz_weights, run
from polymer2 import slope
from polymer3 import summary


def block_weights(seed: int, N: int, L: int):
    rng = random.Random(seed)
    J = N + 3
    mod = 1 << J
    u = pow(3, -1, mod)
    f = []
    while len(f) < N + 2:
        y = rng.getrandbits(J) | 1
        for i in range(L):
            f.append(y * pow(u, i, mod) % mod)
    f = f[: N + 2]

    def w(n, size):
        q = 1 << (n + 2)
        ang = np.array([((f[m] % q) << 53) // q for m in range(size)], dtype=np.float64) / 2.0 ** 53
        return np.exp(-2j * np.pi * ang)
    return w


def main() -> int:
    N, seeds = int(sys.argv[1]), int(sys.argv[2])
    for L in map(int, sys.argv[3:]):
        if L == 0:
            rng = random.Random(77)
            xs = [rng.getrandbits(N + 3) | 1 for _ in range(seeds)]
            summary("L=inf", [slope(run(collatz_weights(xi, N), N), N) for xi in xs])
        else:
            summary(f"L={L}", [slope(run(block_weights(1000 * L + s, N, L), N), N) for s in range(seeds)])
    return 0


if __name__ == "__main__":
    sys.exit(main())
