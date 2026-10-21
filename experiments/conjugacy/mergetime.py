#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Merge-time profile of consecutive pairs (s, s+1), s < 2^j: first step k with T^k s = T^k (s+1), in units of j.
# Window density coal_j(1) counts k <= j; its limit L(1) (genericCoalDensity_tendsto) equals the eventual
# merge density only if the mass at k > j vanishes as j grows.  Split merges at a cycle value (<= 2, "in-phase
# arrival") from merges before the cycle.
import numpy as np, sys
def T(a): return np.where(a&1==1,(3*a+1)>>1,a>>1)
for j in [int(x) for x in sys.argv[1:]]:
    N=2**j; a=np.arange(N,dtype=np.int64); b=a+1
    kmerge=np.full(N,-1,np.int64); atcyc=np.zeros(N,bool)
    for k in range(1, 30*j+1):
        a=T(a); b=T(b)
        m=(a==b)&(kmerge<0)
        kmerge[m]=k; atcyc[m]=(a[m]<=2)
        if (kmerge>=0).sum()+((a<=2)&(b<=2)&(a!=b)).sum()==N: break
    merged=kmerge>=0; pre=merged&~atcyc
    bins=[(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,8),(8,30)]
    row=[f"j={j:2d} pre-cycle merge {pre.mean():.4f} | in-phase cycle {(merged&atcyc).mean():.4f} | never {(~merged).mean():.4f} | pre-cycle merges by k/j:"]
    for lo,hi in bins:
        sel=pre&(kmerge>lo*j)&(kmerge<=hi*j)
        row.append(f"({lo},{hi}] {sel.mean():.4f}")
    print("  ".join(row), flush=True)
    print(f"        coal_j(1) [k<=j, any] = {(merged&(kmerge<=j)).mean():.4f};  mean k/j at pre-cycle merge = {(kmerge[pre]/j).mean():.3f};  in-phase arrivals: mean k/j = {(kmerge[merged&atcyc]/j).mean():.2f}", flush=True)
