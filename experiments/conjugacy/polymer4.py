#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
Is the extra cancellation (collatz slope ~ -0.522 vs random-2-adic null ~ -0.511, polymer3.py)
a property of integer/rational xi, or of the x3 structure x_t = xi 3^{-t} itself?  Runs the
Collatz environment from uniformly random 2-adic starting points xi (J random bits, odd).
Also reports the slope gap at a second N, to see whether it is a finite-size effect.
Usage: polymer4.py N SEEDS
"""
import random
import sys

import numpy as np

from polymer import collatz_weights, run
from polymer2 import slope
from polymer3 import random2adic_weights, summary


def main() -> int:
    N, seeds = int(sys.argv[1]), int(sys.argv[2])
    J = N + 3
    rng = random.Random(77)
    xs = [rng.getrandbits(J) | 1 for _ in range(seeds)]
    c = summary(f"x3, random xi N={N}", [slope(run(collatz_weights(xi, N), N), N) for xi in xs])
    r = summary(f"rand 2-adic N={N}", [slope(run(random2adic_weights(900 + s, N), N), N) for s in range(seeds)])
    se = (c.var(ddof=1) / len(c) + r.var(ddof=1) / len(r)) ** 0.5
    print(f"gap at N={N}: {c.mean() - r.mean():+.5f}  (Welch z = {(c.mean() - r.mean()) / se:+.1f})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
