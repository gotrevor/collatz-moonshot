#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Mixing profile beyond the Terras range: b_{j,t} = mean over n<2^j of (-1)^{T^{j+t}(n)},
split into orbits that have reached {1,2} and those that have not."""
import numpy as np, sys
j = int(sys.argv[1]); T = int(sys.argv[2])
n = np.arange(2**j, dtype=np.uint64); m = n.copy()
incyc = np.zeros(2**j, dtype=bool)
for _ in range(j):
    odd = (m & 1).astype(bool); m = np.where(odd, (3*m+1)>>1, m>>1)
print("t  b_{j,t}   frac_in_cycle   bias_outside_cycle   bias_in_cycle")
for t in range(0, T+1):
    incyc |= (m <= 2)
    s = 1 - 2*(m & 1).astype(np.int64)
    fo = (~incyc).sum(); fi = incyc.sum()
    bo = s[~incyc].mean() if fo else 0.0; bi = s[incyc].mean() if fi else 0.0
    if t % max(1, T//40) == 0 or t < 12:
        print(f"{t:3d} {s.mean():+.6f}  {fi/2**j:.4f}   {bo:+.6f}   {bi:+.5f}")
    odd = (m & 1).astype(bool); m = np.where(odd, (3*m+1)>>1, m>>1)
