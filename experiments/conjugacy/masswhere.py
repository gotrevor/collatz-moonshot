#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
Where does the concentrated L^2 mass sit (massconc.py)?  Every odd xi mod 2^{j+1} is s * 3^k,
s = +-1, k mod 2^{j-1}.  Index the spectrum by the discrete log k and report the mass share
(1) by scale of the signed representative |k| (bins of log2|k|), against the share of
frequencies in that bin, and (2) by popcount of k (as a (j-1)-bit word) outside the resonance window |k| < 64,
against its frequency share there.  Control: shares sum to 1; the |k| <= N window matches chainsup.py's chain values.
"""
import sys

import numpy as np

from wbranch import G


def main() -> int:
    j = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    n = 1 << (j + 1)
    P = 1 << (j - 1)
    g2 = np.abs(G(j)) ** 2
    k = np.zeros(P, dtype=np.int64)
    pw = np.zeros(P, dtype=np.int64)
    x = 1
    for i in range(P):
        pw[i] = x
        x = x * 3 % n
    mass = g2[pw] + g2[(n - pw) % n]  # +3^k and -3^k
    tot = mass.sum()
    print(f"j={j}: total odd mass {tot:.12f} (Parseval: 1)")
    ks = np.arange(P)
    signed = np.where(ks > P // 2, ks - P, ks)
    a = np.abs(signed)
    print("scale bin of |k|      freq share   mass share   ratio")
    bins = [0] + [1 << b for b in range(0, j)]
    for lo, hi in zip(bins[:-1], bins[1:]):
        sel = (a >= lo) & (a < hi) if lo > 0 else (a == 0)
        if sel.sum() == 0:
            continue
        fs, ms = sel.mean(), mass[sel].sum() / tot
        print(f"  [{lo:>7}, {hi:>7})   {fs:10.6f}   {ms:10.6f}   {ms / fs:7.2f}")
    print("popcount of k ((j-1)-bit)   freq share   mass share   ratio")
    pc = np.array([bin(v).count("1") for v in ks])
    far = a >= 64
    print(f"  (excluding the resonance window |k| < 64: {(~far).sum()} frequencies, mass {mass[~far].sum() / tot:.4f})")
    for c in range(j):
        sel = (pc == c) & far
        if sel.sum() == 0:
            continue
        fs, ms = sel.sum() / far.sum(), mass[sel].sum() / mass[far].sum()
        print(f"  {c:>3}   {fs:10.6f}   {ms:10.6f}   {ms / fs:7.2f}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
