#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.11"
# ///
"""Sampled test of ShortIntervalMixing at fixed ratio t/k, far beyond exhaustive range.

For random k-bit n, the two letters at t = rho k, and whether the orbit has reached {1, 2} by t.
Reports max |P(word) - 1/4| over two-letter words, over the stage and over its 4 top-digit bins.
Control with teeth: past C* = 4.82 the cycle tail must break the balance (no 00, no 11), so the
deviation must approach arrived / 4.  Top-digit bins stand in for the sup over m; they do not
replace it."""
import random
import sys
from multiprocessing import Pool

RHOS = [1.0, 1.5, 2.0, 3.0, 4.0, 4.5, 5.0, 6.0]


def worker(arg):
    k, S, seed = arg
    rnd = random.Random(seed)
    times = {int(r * k): i for i, r in enumerate(RHOS)}
    tmax = max(times) + 2
    cnt = [[[0] * 4 for _ in range(4)] for _ in RHOS]  # rho, bin, word
    arr = [0] * len(RHOS)
    for _ in range(S):
        n = (1 << (k - 1)) | rnd.getrandbits(k - 1)
        b = (n >> (k - 3)) & 3
        x, arrived, prev, pend = n, False, 0, None
        for t in range(tmax):
            if x <= 2:
                arrived = True
            bit = x & 1
            if pend is not None:
                cnt[pend][b][2 * prev + bit] += 1
                pend = None
            if t in times:
                i = times[t]
                pend = i
                arr[i] += arrived
            prev = bit
            x = (3 * x + 1) >> 1 if bit else x >> 1
    return cnt, arr


if __name__ == "__main__":
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
    procs = 6
    print(f"S = {S}; noise of a word frequency ~ {0.5 * 3**0.5 / 2 / S**0.5:.4f} overall, twice that per bin")
    print("k     rho  arrived  dev(stage)  dev(worst bin)")
    for k in [24, 50, 100, 200, 400]:
        with Pool(procs) as p:
            rs = p.map(worker, [(k, S // procs, 1000 * k + i) for i in range(procs)])
        for i, rho in enumerate(RHOS):
            c = [[sum(r[0][i][b][w] for r in rs) for w in range(4)] for b in range(4)]
            tot = sum(map(sum, c))
            stage = max(abs(sum(c[b][w] for b in range(4)) / tot - 0.25) for w in range(4))
            worst = max(abs(c[b][w] / sum(c[b]) - 0.25) for w in range(4) for b in range(4))
            print(f"{k:<5} {rho:<4} {sum(r[1][i] for r in rs) / tot:7.4f}  {stage:9.4f}  {worst:9.4f}", flush=True)
