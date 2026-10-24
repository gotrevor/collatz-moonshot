#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Exact characteristic function of the level-(j,a) slice law (research note §11, 2026-10-24).

The slice law: X = sum_k 3^(k-1) 2^(-T_k) in Z/3^a, with T_1 < ... < T_a a uniform a-subset
of [1, j].  This is the law of T^j r over r < 2^j with oddCount r j = a.

Prints sup_{xi coprime to 3} |E e(xi X / 3^a)| for each (j, a).  SliceCharDecay predicts decay
in j along rays a/j = rho for rho below ~0.63 (the threshold 1/log2(3) = 0.631), and no decay
above it, where the slice has fewer than 3^a atoms.

DP over positions t = 1..j: dp[k] is the count of k-subsets of [1, t] by residue; choosing t as
the (k+1)-th element adds 3^k * 2^(-t) mod 3^a.
"""
import sys
from math import comb
import numpy as np


def slice_pmf(j: int, a: int) -> np.ndarray:
    M = 3 ** a
    inv2 = (M + 1) // 2
    dp = [np.zeros(M) for _ in range(a + 1)]
    dp[0][0] = 1.0
    w = 1  # 2^(-t) mod M
    for t in range(1, j + 1):
        w = w * inv2 % M
        for k in range(min(t, a) - 1, -1, -1):
            if k < a - (j - t + 1):  # cannot still reach a elements
                break
            shift = pow(3, k, M) * w % M
            dp[k + 1] += np.roll(dp[k], shift)
    return dp[a] / comb(j, a)


def sup_coprime(pmf: np.ndarray) -> float:
    F = np.abs(np.fft.fft(pmf))
    idx = np.arange(len(pmf))
    return float(F[idx % 3 != 0].max())


def main() -> None:
    jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    amax = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    rhos = [0.35, 0.45, 0.5, 0.55, 0.6, 0.65, 0.75]
    print("j  " + "  ".join(f"rho={r:<5}" for r in rhos))
    for j in range(8, jmax + 1, 2):
        cells = []
        for r in rhos:
            a = round(r * j)
            if a < 2 or a > amax:
                cells.append(" " * 10)
                continue
            cells.append(f"{sup_coprime(slice_pmf(j, a)):.4f}(a{a:<2})"[:10].ljust(10))
        print(f"{j:<3}" + "  ".join(cells), flush=True)


if __name__ == "__main__":
    main()
