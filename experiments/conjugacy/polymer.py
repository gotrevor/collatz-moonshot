#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
Is the fixed-frequency exponent log2|G_n|/n ~ -0.526 (latticerun.py seqs) a property of the
Collatz 2-adic digits, or the quenched free energy of a directed polymer with random unit
complex weights on the same lattice?

Same DP as latticedp.lattice_levels: V_{n+1}(m) = 1/2 V_n(m) + 1/2 w(n, m) V_n(m+1), V_0 = 1,
G_n = V_n(0).  Environments:
  collatz : w(n, m) = e(-<xi 3^{-(m+1)}>_{n+2})  (xi = 1; reproduces latticerun's -0.526)
  iid     : w(n, m) = e(U), U iid uniform  (several seeds)
  iid-pm  : w(n, m) = +-1 iid (real-weight control: positive-mean-zero signs)
Annealed value for every unit-modulus iid environment: E|G_n|^2 = 2^{-n}, i.e. exponent -1/2.
Numerics: values renormalised per level (track log of a running scale), so no underflow.
Usage: polymer.py N SEEDS
"""
import math
import sys

import numpy as np


def run(weights_for_level, N: int) -> list[float]:
    """Return log2|G_n|/n for n = 1..N.  weights_for_level(n, size) -> complex array."""
    V = np.ones(N + 1, dtype=np.complex128)
    logscale = 0.0
    out = []
    for n in range(N):
        w = weights_for_level(n, len(V) - 1)
        V = 0.5 * V[:-1] + 0.5 * w * V[1:]
        s = np.max(np.abs(V))
        V /= s
        logscale += math.log2(s)
        out.append((logscale + math.log2(abs(V[0]))) / (n + 1))
    return out


def collatz_weights(xi: int, N: int):
    J = N + 3
    mod = 1 << J
    u = pow(3, -1, mod)
    f = [(xi * pow(u, m + 1, mod)) % mod for m in range(N + 1)]

    def w(n, size):
        q = 1 << (n + 2)
        ang = np.array([((f[m] % q) << 53) // q for m in range(size)], dtype=np.float64) / 2.0 ** 53
        return np.exp(-2j * np.pi * ang)
    return w


def iid_weights(seed: int):
    rng = np.random.default_rng(seed)
    return lambda n, size: np.exp(2j * np.pi * rng.random(size))


def pm_weights(seed: int):
    rng = np.random.default_rng(seed)
    return lambda n, size: rng.choice([-1.0, 1.0], size).astype(np.complex128)


def main() -> int:
    N, seeds = int(sys.argv[1]), int(sys.argv[2])
    marks = [N // 8 * k for k in range(1, 9)]
    def show(name, r):
        print(f"{name:>12}  " + " ".join(f"{n}:{r[n - 1]:.4f}" for n in marks), flush=True)
    show("collatz xi=1", run(collatz_weights(1, N), N))
    show("collatz xi=5", run(collatz_weights(5, N), N))
    for s in range(seeds):
        show(f"iid s={s}", run(iid_weights(s), N))
    for s in range(min(seeds, 2)):
        show(f"iid+-1 s={s}", run(pm_weights(s), N))
    return 0


if __name__ == "__main__":
    sys.exit(main())
