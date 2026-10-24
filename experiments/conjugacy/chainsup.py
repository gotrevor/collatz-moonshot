#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
Past the FFT's memory range: |G_j(3^k)| * 2^{j/2} on the resonant chain, by a chunked direct sum.

supfreq.py found that for 8 <= j <= 24 the sup over odd xi of |G_j(xi)| sits on +-3^k (k ~ 0.37 j),
with sup |G_j| = 0.104, 0.091, 0.081, 0.075, 0.069, 0.065 at j = 14, 16, ..., 24: decaying, but
the two-step ratio creeps toward 1.  This probe extends the chain maximum to larger j.

Uses antiperiodicity: G_j(xi) = 2^{-j} sum_{s < 2^j} g_j(s) e(xi s / 2^{j+1}) for odd xi.
Control: reproduces supfreq.py's chain values (j = 22, xi = 81: 16.914; j = 24, xi = 3^9: 265.617).
Usage: chainsup.py JMIN JMAX
"""

import sys

import numpy as np

CHUNK = 1 << 22


def chain_coeffs(j: int, ks: list[int]) -> list[complex]:
    n = 1 << (j + 1)
    xis = np.array([3 ** k for k in ks], dtype=np.int64)
    acc = np.zeros(len(ks), dtype=np.complex128)
    for lo in range(0, 1 << j, CHUNK):
        s = np.arange(lo, min(lo + CHUNK, 1 << j), dtype=np.int64)
        x = s.copy()
        for _ in range(j):
            x = np.where(x & 1, (3 * x + 1) >> 1, x >> 1)
        g = np.where(x & 1, -1.0, 1.0)
        for i, xi in enumerate(xis):
            ph = ((xi % n) * s) % n
            acc[i] += np.sum(g * np.exp(2j * np.pi * ph / n))
    return list(acc / (1 << j))


def main() -> int:
    jmin, jmax = int(sys.argv[1]), int(sys.argv[2])
    for j in range(jmin, jmax + 1):
        kc = round(0.37 * j)
        ks = list(range(max(1, kc - 3), kc + 4))
        vals = chain_coeffs(j, ks)
        sc = 2 ** (j / 2)
        best = max(range(len(ks)), key=lambda i: abs(vals[i]))
        row = " ".join(f"3^{k}:{abs(v) * sc:8.3f}" for k, v in zip(ks, vals))
        print(f"j={j:>2}  max k={ks[best]:>2}  S={abs(vals[best]) * sc:9.3f}  "
              f"sup|G|={abs(vals[best]):.4f}  | {row}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
