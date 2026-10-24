#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
Parseval fixes the MEAN of |G_j(xi)|^2 over odd xi at exactly 2^{-j}.  The fixed-frequency rate
2^{-0.524 j} (latticerun.py, polymer*.py) says the TYPICAL value is smaller, so the L^2 mass
must concentrate on few frequencies.  Full FFT, j <= 24: per j, the median of log2|G|^2 / j over
odd xi, the mean (control: exactly -1 in these units), and the fraction of odd frequencies that
carry 50% / 90% of the mass.
"""
import sys

import numpy as np

from wbranch import G


def main() -> int:
    jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    print(f"{'j':>3} {'log2 mean/j':>11} {'median/j':>9} {'frac@50%':>9} {'frac@90%':>9} {'log2 frac50/j':>13}")
    for j in range(8, jmax + 1, 2):
        g = np.abs(G(j)[1::2]) ** 2
        mean = g.mean()
        med = np.median(g)
        s = np.sort(g)[::-1]
        c = np.cumsum(s) / s.sum()
        f50 = (np.searchsorted(c, 0.5) + 1) / len(s)
        f90 = (np.searchsorted(c, 0.9) + 1) / len(s)
        print(f"{j:>3} {np.log2(mean) / j:11.4f} {np.log2(med) / j:9.4f} {f50:9.4f} {f90:9.4f} {np.log2(f50) / j:13.4f}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
