#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.11"
# ///
"""Mean height law: mean log2 T^(Ck) n over stage k against (1 - C beta) k, beta = 1 - log2(3)/2.

Also the single-letter excess X (odd letters at offsets >= k, minus half), and the correction
corr = sum over odd steps of log2(1 + 1/(3 y)).  Identity to check on every start:
log2 T^t n = log2 n - t + O log2 3 + corr.  Control: for C >= 5 the predicted height is negative,
while actual heights are >= 0, so the law must fail there."""
import math
import random
import sys
from multiprocessing import Pool

L3 = math.log2(3)
BETA = 1 - L3 / 2
CS = [2, 3, 4, 5, 6]


def lg(x):
    # log2 of a big int, exact enough
    b = x.bit_length()
    return math.log2(x >> (b - 53)) + (b - 53) if b > 53 else math.log2(x)


def worker(arg):
    k, S, seed = arg
    rnd = random.Random(seed)
    tot = {C: [0.0, 0.0, 0.0] for C in CS}
    worst = 0.0
    tmax = max(CS) * k
    for _ in range(S):
        n = (1 << (k - 1)) | rnd.getrandbits(k - 1)
        x, O, oddk, corr = n, 0, 0, 0.0
        for t in range(tmax + 1):
            if t >= k and t % k == 0 and t // k in tot:
                C = t // k
                h = lg(x)
                worst = max(worst, abs(h - (lg(n) - t + O * L3 + corr)))
                tot[C][0] += h
                tot[C][1] += (O - oddk) - (t - k) / 2
                tot[C][2] += corr
            if t == k:
                oddk = O
                tot_k = O
            if x & 1:
                O += 1
                if t < k:
                    pass
                corr += math.log2(1 + 1 / (3 * x)) if x < (1 << 900) else 0.0
                x = (3 * x + 1) >> 1
            else:
                x >>= 1
    return tot, worst


if __name__ == "__main__":
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 60000
    print(f"S={S}; identity residual reported as max |residual|")
    print("k     C  pred/k  height/k   X/k       corr/k    log2(3)X+corr vs height-pred (per k)")
    for k in [24, 50, 100, 200, 400]:
        with Pool(6) as p:
            rs = p.map(worker, [(k, S // 6, 7000 * k + i) for i in range(6)])
        worst = max(r[1] for r in rs)
        n = 6 * (S // 6)
        for C in CS:
            h, X, c = [sum(r[0][C][i] for r in rs) / n / k for i in range(3)]
            pred = 1 - C * BETA
            print(f"{k:<5} {C}  {pred:+.4f} {h:+.4f}  {X:+.4f}  {c:.5f}   {L3 * X + c:+.4f} vs {h - pred:+.4f}", flush=True)
        print("   identity residual", f"{worst:.2e}")
