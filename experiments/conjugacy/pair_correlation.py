#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""The second-moment route over offsets: van der Corput reduces AveragedMixing to pair correlations
corr(h) = mean over n in stage k, t in [k, Ck) of s(n, t) s(n + h, t), s = (-1)^letter.
The reduction helps only if the average of corr(h) over h <= H tends to 0 with H.
Control: a shift of two independent uniform bit sequences gives corr near 0 at noise 2^(-k/2)/sqrt(k).
Also reports the fraction of pairs merged in phase by t = 2k."""
import sys
import numpy as np

k = int(sys.argv[1]) if len(sys.argv) > 1 else 20
C = 2
a = 1 << (k - 1)
hs = [1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 255, 257, 1023, 1025, 4095, 4097]
H = max(hs)
n = np.arange(a, 2 * a + H + 1, dtype=np.uint64)
N = a
T = C * k
x = n.copy()
sums = {h: 0 for h in hs}
for t in range(T):
    b = (x & np.uint64(1)).astype(np.int8)
    s = 1 - 2 * b
    if t >= k:
        for h in hs:
            sums[h] += int(np.sum(s[:N].astype(np.int64) * s[h:N + h].astype(np.int64)))
    x = np.where(b == 1, (3 * x + np.uint64(1)) >> np.uint64(1), x >> np.uint64(1))
print(f"k={k} C={C}: h, corr(h), merged in phase by t={T}")
cum, cnt = 0.0, 0
for h in hs:
    c = sums[h] / (N * (T - k))
    merged = float(np.mean(x[:N] == x[h:N + h]))
    cum += c
    cnt += 1
    print(f"{h:6d} {c:9.5f} {merged:9.5f}")
rng = np.random.default_rng(1)
ctrl = rng.integers(0, 2, (T - k, N + 1), dtype=np.int8) * 2 - 1
print("control corr(1):", float((ctrl[:, :N].astype(np.int64) * ctrl[:, 1:N + 1]).mean()))
