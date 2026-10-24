#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
The mirror recursion only moves a frequency along its 3-orbit: G_{n+1}(f) = 1/2 G_n(f)
+ 1/2 e(f (1 - 4u) / 2^{n+2}) G_n(u f), u = 3^{-1}.  So G_j(xi) needs only the frequencies
xi * 3^{-m}, m = 0..j, at each level: a lattice DP of size ~ j^2 instead of a 2^{j+1}-term sum.

V_n(m) = G_n(xi * 3^{-m} mod 2^{n+1}),  V_0(m) = 1 (G_0 = 1 at every odd frequency),
V_{n+1}(m) = 1/2 V_n(m) + 1/2 e(f_m (1 - 4u) / 2^{n+2}) V_n(m + 1).

Control (known answer): matches the FFT coefficients (wbranch.G) at j <= 18 for several xi.
Usage: latticedp.py control | latticedp.py run XI JMAX STEP
"""

import cmath
import math
import sys


def lattice_G(xi: int, j: int) -> complex:
    J = j + 3
    mod = 1 << J
    u = pow(3, -1, mod)
    f = [(xi * pow(u, m, mod)) % mod for m in range(j + 1)]
    V = [1 + 0j] * (j + 1)
    for n in range(j):  # level n -> n + 1
        q = 1 << (n + 2)
        c = (1 - 4 * u) % q
        new = [0j] * (j - n)
        for m in range(j - n):
            num = (f[m] * c) % q
            new[m] = 0.5 * V[m] + 0.5 * cmath.exp(2j * math.pi * num / q) * V[m + 1]
        V = new
    return V[0]


def control() -> int:
    from wbranch import G
    worst = 0.0
    for j in range(1, 19):
        Gj = G(j)
        n = 2 ** (j + 1)
        for xi in (1, 3, 5, 7, 27, 81, 243, pow(3, -1, n), n - 1, 12345 % n | 1):
            err = abs(lattice_G(xi, j) - Gj[xi % n])
            worst = max(worst, err)
    print(f"control: max |lattice - FFT| over j <= 18, 10 frequencies each = {worst:.2e}")
    return 0 if worst < 1e-9 else 1


def run(xi: int, jmax: int, step: int) -> int:
    print(f"xi={xi}: j, |G_j|, |G_j| * 2^(j/2)", flush=True)
    for j in range(step, jmax + 1, step):
        g = lattice_G(xi, j)
        print(f"{j:>5} {abs(g):.3e} {abs(g) * 2 ** (j / 2):10.4f}", flush=True)
    return 0


if __name__ == "__main__":
    if sys.argv[1] == "control":
        sys.exit(control())
    sys.exit(run(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])))



def _phase(num: int, q: int) -> complex:
    return cmath.exp(2j * math.pi * ((num << 53) // q) / (1 << 53))


def lattice_levels(xi: int, length: int, top: int) -> tuple[list[complex], list[complex]]:
    """One DP pass.  Returns ([G_n(xi) for n = 0..top], V_top) with V_top(m) = G_top(xi * 3^{-m}),
    m < length - top.  Phases in 53-bit fixed point (exact numerators, rounded angle)."""
    J = top + 3
    mod = 1 << J
    u = pow(3, -1, mod)
    f = [(xi * pow(u, m, mod)) % mod for m in range(length)]
    V = [1 + 0j] * length
    g0 = [V[0]]
    for n in range(top):
        q = 1 << (n + 2)
        c = (1 - 4 * u) % q
        V = [0.5 * V[m] + 0.5 * _phase((f[m] * c) % q, q) * V[m + 1] for m in range(len(V) - 1)]
        g0.append(V[0])
    return g0, V
