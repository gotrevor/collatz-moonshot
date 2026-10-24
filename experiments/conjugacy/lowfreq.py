#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
LowFreqDecay: does each fixed Fourier coefficient G_j(xi) of the beyond-Terras sign tend to 0?
And the reduction  |b_j| <= sum_{odd |xi| <= K} |G_j(xi)| / |xi| + sqrt(2/K)   (Parseval + Cauchy-Schwarz),
checked with teeth: the right side must dominate |b_j| for every K, and the inequality without the
sqrt(2/K) tail must FAIL somewhere (else the tail term is not doing work and the check is weak).
"""

import sys

import numpy as np

from wbranch import G, signs


def main() -> int:
    jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    xs = [1, 3, 5, 7, 9, 15, 27, 81]
    print("|G_j(xi)| * 2^{j/2} for fixed odd xi (signed residues: xi and -xi pooled by max)")
    print(f"{'j':>3} " + " ".join(f"{x:>7}" for x in xs) + f" {'|b_j|':>9} {'min slack':>9} {'tailless fails':>14}")
    for j in range(4, jmax + 1):
        Gj = G(j)
        n = 2 ** (j + 1)
        vals = [max(abs(Gj[x % n]), abs(Gj[(-x) % n])) * 2 ** (j / 2) for x in xs]
        b = abs(signs(j)[: 2 ** j].sum()) / 2 ** j
        slack = []
        tailless_fail = False
        for K in [1, 3, 9, 27, 81, 243, 729]:
            if K > n // 2:
                break
            odd = [x for x in range(1, K + 1, 2)]
            low = sum((abs(Gj[x % n]) + abs(Gj[(-x) % n])) / x for x in odd)
            rhs = low + np.sqrt(2.0 / K)
            slack.append(rhs - b)
            if low < b:
                tailless_fail = True
        print(f"{j:>3} " + " ".join(f"{v:7.3f}" for v in vals) + f" {b:9.5f} {min(slack):9.4f} {str(tailless_fail):>14}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
