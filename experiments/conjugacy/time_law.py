#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.11"
# ///
"""Time law: first t with T^t n <= f(n), per bit, against 1/beta = 4.8188.

f(n) = k = bit length, f(n) = 1000, and f = 2 (total stopping, in T steps).  Known answer: the
stochastic model's total stopping time, (2 / ln(4/3)) ln n = 4.8188 k.  Control: passage to n^0.5 must
sit at 0.5/beta = 2.409, not at 1/beta."""
import math
import random
import sys
from multiprocessing import Pool

BETA = 1 - math.log2(3) / 2


def worker(arg):
    k, seed = arg
    n = random.Random(seed).getrandbits(k) | (1 << (k - 1)) | 1
    half = 1 << (k // 2)
    hit = {"n^0.5": None, "k": None, "1000": None, "2": None}
    t, y = 0, n
    while hit["2"] is None:
        if hit["n^0.5"] is None and y <= half:
            hit["n^0.5"] = t / k
        if hit["k"] is None and y <= k:
            hit["k"] = t / k
        if hit["1000"] is None and y <= 1000:
            hit["1000"] = t / k
        if y <= 2:
            hit["2"] = t / k
        y = y // 2 if y % 2 == 0 else (3 * y + 1) // 2
        t += 1
    return hit


if __name__ == "__main__":
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    print(f"1/beta={1/BETA:.4f}  0.5/beta={0.5/BETA:.4f}")
    with Pool(6) as p:
        for k in [500, 2000, 8000, 20000]:
            res = p.map(worker, [(k, 7000 * k + s) for s in range(S)])
            for key in ["n^0.5", "k", "1000", "2"]:
                v = [r[key] for r in res]
                print(f"k={k} S={S} t/k to {key}: min {min(v):.3f} mean {sum(v)/S:.3f} max {max(v):.3f}")
            sys.stdout.flush()
