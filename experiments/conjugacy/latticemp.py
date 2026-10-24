#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""High-precision cross-check of latticedp.lattice_levels (floats) at long range.

Same DP with mpmath at 60 digits.  Prints log2|G_n(xi)| / n from both; agreement checks that the
float run's tiny values (|G_n(1)| ~ 2^{-0.525 n}) are not rounding artefacts.
Usage: latticemp.py XI N1 N2 ...
"""
import math
import sys

import mpmath as mp

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from latticedp import lattice_levels  # noqa: E402

mp.mp.dps = 60


def mp_levels(xi: int, top: int) -> list:
    J = top + 3
    mod = 1 << J
    u = pow(3, -1, mod)
    f = [(xi * pow(u, m, mod)) % mod for m in range(top + 1)]
    V = [mp.mpc(1)] * (top + 1)
    g0 = [V[0]]
    for n in range(top):
        q = 1 << (n + 2)
        c = (1 - 4 * u) % q
        V = [(V[m] + mp.expjpi(2 * mp.mpf((f[m] * c) % q) / q) * V[m + 1]) / 2 for m in range(len(V) - 1)]
        g0.append(V[0])
    return g0


def main() -> int:
    xi = int(sys.argv[1])
    ns = [int(a) for a in sys.argv[2:]]
    top = max(ns)
    hp = mp_levels(xi, top)
    fl, _ = lattice_levels(xi, top + 1, top)
    for n in ns:
        a = float(mp.log(abs(hp[n]), 2)) / n
        b = math.log2(abs(fl[n])) / n if fl[n] != 0 else float("nan")
        rel = float(abs(hp[n] - fl[n]) / abs(hp[n]))
        print(f"xi={xi} n={n:>5}  log2|G|/n  mp={a:.6f}  float={b:.6f}  rel.err={rel:.1e}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
