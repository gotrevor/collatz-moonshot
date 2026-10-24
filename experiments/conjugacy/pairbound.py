#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
Tao-style pairing bound (mirror of Tao 2019 eq. 7.5 / Lemma 7.2) for the lattice sum.

G_n(xi) = E_S e(-sum_t Theta(s_t + 2, t)), S uniform subset of {0..n-1}, s_1 > s_2 > ..., and
Theta(k, t) = <xi 3^{-t}>_k.  Pair levels into blocks {2i+1, 2i}.  Given how many elements of S
each block holds, the blocks are independent; a block holding exactly one element (t) averages
levels k = 2i+3 and 2i+2, and Theta(2i+2, t) = 2 Theta(2i+3, t) mod 1, so its factor has modulus
|cos(pi Theta(2i+3, t))|.  Hence |G_n| <= U_n, with U_n a POSITIVE lattice walk:
  blocks top-down; count 0 (prob 1/4): t stays; count 2 (prob 1/4): t += 2, weight 1;
  count 1 (prob 1/2): weight |cos(pi Theta(2i+3, t+1))|, t += 1.
Teeth: U_n >= |G_n| must hold (checked against latticedp at every even n <= 200, several xi).
Usage: pairbound.py check | pairbound.py run N
"""
import math
import random
import sys

import numpy as np

from latticedp import lattice_levels


def pair_bound(xi: int, n: int) -> float:
    assert n % 2 == 0
    J = n + 4
    mod = 1 << J
    u = pow(3, -1, mod)
    x = [(xi * pow(u, t, mod)) % mod for t in range(n + 2)]  # x[t] = xi 3^{-t}
    W = np.zeros(n + 2)
    W[0] = 1.0  # W[t] = weight of having used t elements so far
    for i in range(n // 2 - 1, -1, -1):
        k = 2 * i + 3
        q = 1 << k
        c = np.array([abs(math.cos(math.pi * (((x[t + 1] % q) << 53) // q) / 2.0 ** 53)) for t in range(n + 1)])
        new = 0.25 * W
        new[2:] += 0.25 * W[:-2]
        new[1:] += 0.5 * (W[:-1] * c[: n + 1])
        W = new
    return float(W.sum())


def check() -> int:
    worst = math.inf
    for xi in (1, 5, 7, 27, 81, 3 ** 10, 12345):
        g0, _ = lattice_levels(xi, 201, 200)
        for n in range(2, 201, 2):
            worst = min(worst, pair_bound(xi, n) - abs(g0[n]))
    print(f"check: min over xi, even n <= 200 of (U_n - |G_n|) = {worst:.3e}  (must be >= 0)")
    return 0 if worst >= -1e-12 else 1


def run(N: int) -> int:
    rng = random.Random(5)
    panel = [("1", 1), ("5", 5), ("27", 27), ("rand", rng.getrandbits(N + 4) | 1)]
    for name, xi in panel:
        row = " ".join(f"{n}:{math.log2(pair_bound(xi, n)) / n:.4f}" for n in range(N // 4, N + 1, N // 4))
        print(f"xi={name:>5}  log2 U_n / n  {row}", flush=True)
    for n in (64, 256, 1024):
        print(f"resonant xi=3^(n/2), n={n}: U_n = {pair_bound(3 ** (n // 2), n):.4e}  (|G| ~ 0.227/sqrt(n) = {0.227 / n ** 0.5:.4e})", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(check() if sys.argv[1] == "check" else run(int(sys.argv[2])))
