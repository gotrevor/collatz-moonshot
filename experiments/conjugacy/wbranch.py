#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
Does the weighted Fourier criterion W_j -> 0 (section 10.6) close by a triangle-inequality
recursion, or does a proof of BiasDecays need cancellation between the two branches?

g_j(r) = (-1)^{T^j r} on Z/2^{j+1} (2^j-antiperiodic).  G_j(xi) = 2^{-(j+1)} sum_r g_j(r) e(xi r / 2^{j+1}).
W_j = 2^{-j} sum_{xi odd} |G_j(xi)| / sin(pi xi / 2^{j+1})          (|bias_j| / 2^j <= W_j)
Mirror recursion: G_j(xi) = 1/2 [G_{j-1}(xi) + phase * G_{j-1}(u xi)],  u = 3^{-1} mod 2^{j+1}.

Branch weights (triangle inequality):
  A_j = 2^{-j} sum_xi (1/2)|G_{j-1}(xi)|   / sin(pi xi/2^{j+1})     (doc: exactly <= W_{j-1}/sqrt 2)
  B_j = 2^{-j} sum_xi (1/2)|G_{j-1}(u xi)| / sin(pi xi/2^{j+1})
If (A_j + B_j) / W_{j-1} >= 1 the triangle route gives no contraction.

Control: W_j must reproduce section 10.6 (0.290, 0.173, 0.090, 0.052, 0.029, 0.015, 0.0078, 0.0047
at j = 8, 10, ..., 22) and |E_j|/2^j <= W_j must hold.
"""

import sys

import numpy as np


def signs(j: int) -> np.ndarray:
    r = np.arange(2 ** (j + 1), dtype=np.int64)
    x = r.copy()
    for _ in range(j):
        odd = x & 1
        x = np.where(odd == 1, (3 * x + 1) >> 1, x >> 1)
    return np.where(x & 1, -1.0, 1.0)


def G(j: int) -> np.ndarray:
    g = signs(j)
    n = 2 ** (j + 1)
    # G(xi) = n^{-1} sum_r g(r) e(+xi r / n)  ->  numpy ifft computes n^{-1} sum g e(+...)
    return np.fft.ifft(g)


def weight(j: int) -> np.ndarray:
    n = 2 ** (j + 1)
    xi = np.arange(n)
    w = np.zeros(n)
    odd = xi % 2 == 1
    w[odd] = 1.0 / np.sin(np.pi * xi[odd] / n)
    return w


def main() -> int:
    jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    print(f"{'j':>3} {'|E|/2^j':>9} {'W_j':>8} {'W/Wprev':>8} {'A/Wprev':>8} {'B/Wprev':>8} {'(A+B)/Wp':>9} {'recur err':>9}")
    prevG = None
    prevW = None
    for j in range(2, jmax + 1):
        Gj = G(j)
        n = 2 ** (j + 1)
        w = weight(j)
        W = (2.0 ** -j) * np.sum(np.abs(Gj) * w)
        E = signs(j)[: 2 ** j].sum()
        line = f"{j:>3} {abs(E) / 2 ** j:9.5f} {W:8.5f}"
        if prevG is not None:
            u = pow(3, -1, n)
            xi = np.arange(n)
            Gp_xi = prevG[xi % (n // 2)]
            Gp_uxi = prevG[(u * xi) % n % (n // 2)]
            A = (2.0 ** -j) * np.sum(0.5 * np.abs(Gp_xi) * w)
            B = (2.0 ** -j) * np.sum(0.5 * np.abs(Gp_uxi) * w)
            # recursion check on magnitudes: |G_j| <= (|G_{j-1}(xi)| + |G_{j-1}(u xi)|)/2
            viol = np.max(np.abs(Gj)[xi % 2 == 1] - 0.5 * (np.abs(Gp_xi) + np.abs(Gp_uxi))[xi % 2 == 1])
            line += f" {W / prevW:8.4f} {A / prevW:8.4f} {B / prevW:8.4f} {(A + B) / prevW:9.4f} {viol:9.2e}"
        print(line, flush=True)
        prevG, prevW = Gj, W
    return 0


if __name__ == "__main__":
    sys.exit(main())
