#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Tao's (7.5) damping bound at pair-sum law Pascal(p) (research note §11, 2026-10-24).

D(n, p) = sup_{3 ∤ ξ} E_{b ~ Pascal(p)^{n/2}} ∏_j |f(x_j, b_j)|, with
f(x, b) = (b−1)^{-1} Σ_{a=1}^{b−1} e(−x(2^a + 3)/3^n), x_j = 3^{2j} 2^{−(b_1+…+b_{j+1})}
(tao-collatz Sec7/Reduction.lean: fCond, xArg, cexpect_pairing_gen).  Pascal(p) is the law of
a sum of two iid Geom(p) gaps: P(b) = (b−1) p² (1−p)^{b−2}.  At p = 1/2 this is Tao's bound,
which decays like n^{−A}.  SliceCharDecay needs it to decay for p up to 3/5; the heuristic
threshold is p = 1/log₂3 ≈ 0.631.

Units mod 3^n are ±2^k, so sup over ξ is a sup over the starting prefix offset; a backward DP
over the prefix residue l mod 2·3^{n−1} (the order of 2) gives every offset at once.
"""
import sys
import numpy as np


def damping(n: int, p: float, tail: float = 1e-10) -> float:
    M = 3 ** n
    per = 2 * 3 ** (n - 1)
    inv2 = (M + 1) // 2
    pw = np.empty(per, dtype=np.int64)  # 2^{-l} mod M
    pw[0] = 1
    for l in range(1, per):
        pw[l] = pw[l - 1] * inv2 % M
    q = 1 - p
    B = 2
    while (B - 1) * p * p * q ** (B - 2) > tail or B < 4:
        B += 1
    probs = [(b - 1) * p * p * q ** (b - 2) for b in range(B + 1)]
    V = np.ones(per)
    for j in reversed(range(n // 2)):
        x = pow(3, 2 * j, M) * pw % M  # x_j as a function of the prefix l
        newV = np.zeros(per)
        S = np.zeros(per, dtype=complex)
        t = 2 * x % M  # x·2^a, a = 1
        for b in range(2, B + 1):
            S += np.exp(-2j * np.pi * t / M)  # adds a = b−1
            t = t * 2 % M
            Fb = np.abs(S) / (b - 1)  # |f(x(l'), b)| at prefix l'
            # V_j(l) += P(b) |f(x(l+b), b)| V_{j+1}(l+b)
            newV += probs[b] * np.roll(Fb * V, -b)
        V = newV
    return float(V.max())


def main() -> None:
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    ps = [0.35, 0.45, 0.5, 0.55, 0.6, 0.65, 0.7, 0.8]
    print("n   " + "  ".join(f"p={p:<5}" for p in ps))
    for n in range(4, nmax + 1, 2):
        print(f"{n:<4}" + "  ".join(f"{damping(n, p):.5f}" for p in ps), flush=True)


if __name__ == "__main__":
    main()
