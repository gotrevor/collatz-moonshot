#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""
NoLongRuns: is ||Theta(k, t)|| >= (k + t)^{-C} for a fixed C (fixed odd xi, 3^t not dividing xi,
2^k > 4 xi)?  Reports the empirical exponent C_emp = max log(1/||Theta||) / log(k + t) over the
field k <= K, t <= K/2 (same field as traps.py), the point where it is attained, and C_emp
restricted to k + t >= 100, 1000 (does it creep upward?).  A random-field model with
Borel-Cantelli predicts finitely many violations for any C > 2.
Control: xi = 3^20 (resonant columns t <= 20 excluded by the 3^t | xi rule; the rest must look
like the others).
Usage: runs.py K XI...
"""
import math
import sys

import numpy as np

from traps import field


def main() -> int:
    K = int(sys.argv[1])
    T = K // 2
    for a in sys.argv[2:]:
        xi = 3 ** int(a[2:]) if a.startswith("3^") else int(a)
        D = field(xi, K, T)
        v3 = 0
        while xi % 3 ** (v3 + 1) == 0:
            v3 += 1
        k = np.arange(K + 1)[:, None]
        t = np.arange(T + 1)[None, :]
        ok = (t > v3) & ((2.0 ** np.minimum(k, 1000)) > 4 * xi) & (D > 0)
        with np.errstate(divide="ignore"):
            C = np.where(ok, np.log(1 / np.where(D > 0, D, 1)) / np.log(k + t), -np.inf)
        row = []
        for lo in (0, 100, 1000):
            Cm = np.where(k + t >= lo, C, -np.inf)
            i = np.unravel_index(np.argmax(Cm), Cm.shape)
            row.append(f"k+t>={lo}: C={Cm[i]:.3f} at (k={i[0]}, t={i[1]})")
        print(f"xi={a:>6}  " + "  ".join(row), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
