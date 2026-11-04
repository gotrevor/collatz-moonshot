#!/usr/bin/env -S uv run --quiet --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Exact sup over m of |#{n in first m of stage k : letter t = 0} - m/2| / 2^(k-1), the error in
ShortIntervalMixing at L = 1.  Controls: t <= k-10 must obey the proved bound 2^t / 2^(k-1), and
a random +/-1 sequence gives the scale sqrt(2^(k-1)) / 2^(k-1) of a walk."""
import sys
import numpy as np

kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 24
rng = np.random.default_rng(1)


def sup_err(bits):
    s = np.cumsum(1 - 2 * bits.astype(np.int64))  # +1 even, -1 odd; count - m/2 = S/2
    return float(np.abs(s).max()) / 2 / len(bits)


print("k    walk  | " + "".join(f"{lab:>9}" for lab in
      ["k-10", "bound", "k", "k+1", "k+2", "k+4", "k+8", "1.5k", "2k", "3k", "4k"]))
for k in range(14, kmax + 1, 2):
    a = 1 << (k - 1)
    n = np.arange(a, 2 * a, dtype=np.uint64)
    x = n.copy()
    want = {"k-10": k - 10, "k": k, "k+1": k + 1, "k+2": k + 2, "k+4": k + 4, "k+8": k + 8,
            "1.5k": (3 * k) // 2, "2k": 2 * k, "3k": 3 * k, "4k": 4 * k}
    res = {}
    for t in range(4 * k + 1):
        b = x & np.uint64(1)
        for lab, tt in want.items():
            if tt == t:
                res[lab] = sup_err(b.astype(np.uint8))
        x = np.where(b == 1, (3 * x + np.uint64(1)) >> np.uint64(1), x >> np.uint64(1))
    assert int(x.max()) < 2**63
    walk = sup_err(rng.integers(0, 2, a, dtype=np.uint8))
    bound = 2.0 ** (k - 10) / a
    print(f"{k:<4} {walk:.4f}| " + "".join(f"{res[l]:9.4f}" if l != "bound" else f"{bound:9.4f}"
          for l in ["k-10", "bound", "k", "k+1", "k+2", "k+4", "k+8", "1.5k", "2k", "3k", "4k"]))
