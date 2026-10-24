#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
Is the decay of G_j uniform in the frequency?  sup_{odd xi} |G_j(xi)| -> 0 would imply
TwoAdicFreqDecay (and LowFreqDecay) at once, as a single uniform node.

Prints S_j = max_{odd xi} |G_j(xi)| * 2^{j/2}, the signed argmax xi (and xi * 3^{-k} for the k
that makes it smallest, to see whether the max sits on the 3^k chain or its 2-adic orbit).

Control (known answer): S_j >= the chain values from lowfreq.py (xi = 81: 16.9 at j = 22,
xi = 27: 7.8 at j = 13), and |G_j(1)| * 2^{j/2} matches lowfreq.py's xi = 1 column.
"""

import sys

import numpy as np

from wbranch import G


def signed(x: int, n: int) -> int:
    return x - n if x > n // 2 else x


def main() -> int:
    jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    print(f"{'j':>3} {'S_j':>8} {'argmax xi':>12} {'3-orbit min':>14} {'G(1)':>7} {'G(27)':>7} {'G(81)':>7}")
    for j in range(2, jmax + 1):
        Gj = G(j)
        n = 2 ** (j + 1)
        a = np.abs(Gj).copy()
        a[0::2] = 0.0
        xi = int(np.argmax(a))
        s = a[xi] * 2 ** (j / 2)
        # smallest signed representative along the orbit xi * 3^{-k}, k = 0..2j
        u = pow(3, -1, n)
        best, bestk, x = signed(xi, n), 0, xi
        for k in range(1, 2 * j + 1):
            x = (x * u) % n
            if abs(signed(x, n)) < abs(best):
                best, bestk = signed(x, n), k
        sc = 2 ** (j / 2)
        print(f"{j:>3} {s:8.3f} {signed(xi, n):>12} {f'{best}*3^{bestk}':>14} "
              f"{abs(Gj[1]) * sc:7.3f} {abs(Gj[27 % n]) * sc:7.3f} {abs(Gj[81 % n]) * sc:7.3f}",
              flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
