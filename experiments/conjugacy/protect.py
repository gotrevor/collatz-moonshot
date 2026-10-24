#!/usr/bin/env -S uv run --quiet python3
"""
Protection lemma (the mirror of Tao 2019 eq. 7.16): for odd xi, t >= 1 with 3^t not dividing xi,
and 2^k > xi,  ||Theta(k, t)|| >= (1 - xi/2^k) / 3^t,  Theta(k, t) = <xi 3^{-t}>_k.
Proof: q x = p + 2^k m with q = 3^t, p = xi, x = xi q^{-1} mod 2^k; so Theta = m/q + p/(q 2^k),
and m = 0 mod q iff q | p.
Check: exhaustive over xi in a panel, t <= 12, k <= 40; reports the minimum of
||Theta|| * 3^t / (1 - xi/2^k) (must be >= 1) and that equality-tightness occurs (teeth: the
ratio's minimum should be close to 1, else the bound is slack and the check proves little),
and the resonant failure xi = 3^5 at t <= 5.
"""
from fractions import Fraction


def theta(xi: int, k: int, t: int) -> Fraction:
    m = 1 << k
    return Fraction((xi * pow(3, -t, m)) % m, m)


def dist(f: Fraction) -> Fraction:
    f -= int(f)
    return min(f, 1 - f)


worst = None
for xi in (1, 5, 7, 11, 25, 101, 3 * 5, 9 * 7):
    for t in range(1, 13):
        if xi % 3 ** t == 0:
            continue
        for k in range(xi.bit_length() + 1, 41):
            r = dist(theta(xi, k, t)) * 3 ** t / (1 - Fraction(xi, 1 << k))
            worst = r if worst is None or r < worst else worst
print(f"min ratio (must be >= 1): {float(worst):.6f}")
print("resonant xi = 3^5: ||Theta(30, t)|| for t = 1..6:",
      [f"{float(dist(theta(3 ** 5, 30, t))):.2e}" for t in range(1, 7)])
