#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
TwoAdicFreqDecay: for a fixed odd 2-adic integer eta, does G_j(eta mod 2^{j+1}) -> 0?
Integer eta is LowFreqDecay; eta = xi/3 are the third points that feed it through the mirror
recursion (|G_j(xi)| <= sum_m 2^{-m} |G_{j-m}(xi/3)| + 2^{-j}).  A random 2-adic unit is the
generic control.  Prints |G_j(eta mod 2^{j+1})| * 2^{j/2}.
"""

import random
import sys

from wbranch import G


def two_adic(num: int, den: int, k: int) -> int:
    m = 2 ** k
    return (num * pow(den, -1, m)) % m


def main() -> int:
    jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    rng = random.Random(20261024)
    rand_bits = rng.getrandbits(64) | 1
    etas = [("1", 1, 1), ("1/3", 1, 3), ("-1/3", -1, 3), ("1/9", 1, 9), ("5/7", 5, 7), ("1/27", 1, 27)]
    print(f"{'j':>3} " + " ".join(f"{n:>7}" for n, _, _ in etas) + f" {'random':>7}")
    for j in range(4, jmax + 1):
        Gj = G(j)
        n = 2 ** (j + 1)
        vals = [abs(Gj[two_adic(a, b, j + 1)]) * 2 ** (j / 2) for _, a, b in etas]
        vals.append(abs(Gj[rand_bits % n]) * 2 ** (j / 2))
        print(f"{j:>3} " + " ".join(f"{v:7.3f}" for v in vals), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
