#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Autocorrelation of the beyond-Terras letter sign g_j(r) = (-1)^{T^j r} over one period r mod 2^(j+1):
# R_j(d) = 2^-(j+1) sum_r g(r) g(r+d).  Exact: R(0)=1, R(2^j) = -1.
import numpy as np, sys
j=int(sys.argv[1]); N=2**(j+1); y=np.arange(N, dtype=np.int64)
for _ in range(j): odd=(y&1).astype(bool); y=np.where(odd,(3*y+1)>>1,y>>1)
g=(1-2*(y&1)).astype(np.float64)
def R(d): return float((g*np.roll(g,-d)).mean())
print(f"j={j}  R(d) for d=1..16: "+" ".join(f"{R(d):+.3f}" for d in range(1,17)))
print(f"      R(2^i), i=0..{j}: "+" ".join(f"{R(2**i):+.3f}" for i in range(0,j+1)))
print(f"      R(3*2^i), i=0..{j-1}: "+" ".join(f"{R(3*2**i):+.3f}" for i in range(0,j)))
print(f"      R(odd d) mean over d<256: {np.mean([R(d) for d in range(1,256,2)]):+.4f};  R(even d) mean: {np.mean([R(d) for d in range(2,256,2)]):+.4f}")
# spectral mass: sum over all lags of R(d) (= variance of the full-period sum / N = 0 exactly); partial sums up to lag D
for D in (2**6, 2**10, 2**14, 2**(j//2), 2**(j-2)):
    if D<N//2: print(f"      1+2*sum_{{d<={D}}} R(d) (block-variance factor at length ~{D}): {1+2*sum(R(d) for d in range(1,D+1)):.2f}")
