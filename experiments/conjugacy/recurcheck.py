#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Exact complex check of the mirror recursion as frozen in Fourier.lean (fourierCoeff_succ):
G_{j+1}(xi) = 1/2 G_j(xi) + 1/2 e(xi (1 - 4u) / 2^{j+2}) G_j(u xi),  3u = 1 mod 2^{j+1},
with G_j(xi) = 2^{-(j+1)} sum_{r < 2^{j+1}} (-1)^{T^j r} e(xi r / 2^{j+1}).  Teeth: the same identity
with the phase dropped must fail."""
import numpy as np
from wbranch import G

worst, worst_nophase = 0.0, 0.0
for j in range(1, 18):
    Gj, Gj1 = G(j), G(j + 1)
    n, n1 = 2 ** (j + 1), 2 ** (j + 2)
    u = pow(3, -1, n)
    for xi in range(0, n1):
        ph = np.exp(2j * np.pi * xi * (1 - 4 * u) / n1)
        rhs = 0.5 * Gj[xi % n] + 0.5 * ph * Gj[(u * xi) % n]
        worst = max(worst, abs(Gj1[xi] - rhs))
        worst_nophase = max(worst_nophase, abs(Gj1[xi] - 0.5 * Gj[xi % n] - 0.5 * Gj[(u * xi) % n]))
print(f"max error with phase: {worst:.2e}   without phase (teeth): {worst_nophase:.2e}")
