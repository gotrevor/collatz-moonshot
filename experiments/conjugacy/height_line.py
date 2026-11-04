#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.11"
# ///
"""Height line: sup over t <= tau k of |log2 T^t n - (log2 n - beta t)| / k, beta = 1 - log2(3)/2.

Should shrink with k for tau below 1/beta = 4.82, and first passage below n^theta should sit at
t/k = (1 - theta)/beta.  Control: at tau = 5 > 1/beta the line goes negative while heights stay
>= 0, so the sup must stay near 5 beta - 1 = 0.0375 however large k is.  Known answer: the referee's
t/k = 4.18-4.42 to height N^0.1 at k = 20000."""
import math
import random
import sys
from multiprocessing import Pool

BETA = 1 - math.log2(3) / 2
TAUS = [4.0, 4.5, 4.7, 5.0]
THETAS = [0.5, 0.17, 0.1, 0.05]


def lg(x):
    b = x.bit_length()
    return math.log2(x >> (b - 53)) + (b - 53) if b > 53 else math.log2(x)


def worker(arg):
    k, seed = arg
    rnd = random.Random(seed)
    n = rnd.getrandbits(k) | (1 << (k - 1)) | 1
    ln = lg(n)
    sup = {tau: 0.0 for tau in TAUS}
    hit = {th: None for th in THETAS}
    y = n
    for t in range(0, int(max(TAUS) * k) + 1):
        h = lg(y)
        dev = abs(h - (ln - BETA * t)) / k
        for tau in TAUS:
            if t <= tau * k and dev > sup[tau]:
                sup[tau] = dev
        for th in THETAS:
            if hit[th] is None and h <= th * ln:
                hit[th] = t / k
        y = y // 2 if y % 2 == 0 else (3 * y + 1) // 2
        if y == 1:
            y = 2  # stay on the 1,2 cycle; height is then <= 1
    return sup, hit


if __name__ == "__main__":
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    print(f"beta={BETA:.5f}  1/beta={1/BETA:.4f}")
    for th in THETAS:
        print(f"predicted t/k to n^{th}: {(1 - th) / BETA:.3f}")
    with Pool(6) as p:
        for k in [500, 2000, 8000, 20000]:
            res = p.map(worker, [(k, 1000 * k + s) for s in range(S)])
            sups = {tau: [r[0][tau] for r in res] for tau in TAUS}
            line = " ".join(f"tau={tau}: mean {sum(v)/S:.4f} max {max(v):.4f}" for tau, v in sups.items())
            print(f"k={k} S={S} sup/k  {line}")
            for th in THETAS:
                v = [r[1][th] for r in res if r[1][th] is not None]
                miss = S - len(v)
                if v:
                    print(f"   t/k to n^{th}: min {min(v):.3f} mean {sum(v)/len(v):.3f} max {max(v):.3f}  not reached by 5k: {miss}")
                else:
                    print(f"   t/k to n^{th}: none reached by 5k")
            sys.stdout.flush()
