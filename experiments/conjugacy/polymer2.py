#!/usr/bin/env -S uv run --quiet --with numpy python3
"""
Slope estimate of log2|G_n| over n in [N/2, N] (least squares), which removes O(1) offsets and
damps accidental near-zeros of V[0].  Collatz panel (7 frequencies, as latticerun.py seqs) vs
iid uniform phases (many seeds) on the same lattice.  Uses polymer.run/collatz_weights.
Usage: polymer2.py N SEEDS
"""
import random
import sys

import numpy as np

from polymer import collatz_weights, iid_weights, run


def slope(r: list[float], N: int) -> float:
    n = np.arange(N // 2, N + 1)
    y = np.array([r[k - 1] * k for k in n])  # log2|G_n|
    return float(np.polyfit(n, y, 1)[0])


def main() -> int:
    N, seeds = int(sys.argv[1]), int(sys.argv[2])
    mod = 1 << (N + 3)
    rnd = random.Random(20261024).getrandbits(64) | 1
    panel = [("1", 1), ("5", 5), ("7", 7), ("27", 27), ("1/3", pow(3, -1, mod)),
             ("5/7", 5 * pow(7, -1, mod) % mod), ("rand64", rnd)]
    cs = []
    for name, xi in panel:
        s = slope(run(collatz_weights(xi, N), N), N)
        cs.append(s)
        print(f"collatz {name:>7}: slope {s:.5f}", flush=True)
    iid = [slope(run(iid_weights(100 + s), N), N) for s in range(seeds)]
    cs, iid = np.array(cs), np.array(iid)
    print(f"collatz panel: mean {cs.mean():.5f}  sd {cs.std(ddof=1):.5f}  n={len(cs)}")
    print(f"iid seeds    : mean {iid.mean():.5f}  sd {iid.std(ddof=1):.5f}  n={len(iid)}  "
          f"min {iid.min():.5f} max {iid.max():.5f}")
    se = (cs.var(ddof=1) / len(cs) + iid.var(ddof=1) / len(iid)) ** 0.5
    print(f"difference {cs.mean() - iid.mean():.5f}  (Welch z = {(cs.mean() - iid.mean()) / se:.1f})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
