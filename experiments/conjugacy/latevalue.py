#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Where do the late merges happen?  For consecutive pairs (s, s+1), s < 2^j, record the first merge step k and
# the merge value m = T^k s.  Compare log2(m)/j for merges inside the window (k <= j) and beyond it (k > j, m > 2).
# Hypothesis: late merges happen in the descent phase at values far below 2^j - integers are zero-tailed 2-adic
# numbers, so their orbits beyond step j are orbits of small numbers, which the window limit (a Haar measure
# over generic starts) never sees.
import numpy as np, sys
def T(a): return np.where(a&1==1,(3*a+1)>>1,a>>1)
for j in [int(x) for x in sys.argv[1:]]:
    N=2**j; a=np.arange(N,dtype=np.int64); b=a+1
    kmerge=np.full(N,-1,np.int64); mval=np.zeros(N,np.int64)
    for k in range(1, 30*j+1):
        a=T(a); b=T(b)
        m=(a==b)&(kmerge<0); kmerge[m]=k; mval[m]=a[m]
        if (kmerge>=0).sum()+((a<=2)&(b<=2)&(a!=b)).sum()==N: break
    early=(kmerge>=1)&(kmerge<=j)&(mval>2); late=(kmerge>j)&(mval>2)
    le=np.log2(mval[early].astype(float))/j; ll=np.log2(mval[late].astype(float))/j
    # peak value before the merge is not tracked; the merge value itself is the diagnostic
    q=lambda x: " ".join(f"{np.percentile(x,p):.2f}" for p in (10,25,50,75,90))
    print(f"j={j}: early merges {early.mean():.4f} (log2 m / j pct 10/25/50/75/90: {q(le)});  late merges {late.mean():.4f} (log2 m / j: {q(ll)});  late with m < 2^(j/2): {(np.log2(mval[late].astype(float))<j/2).mean():.3f};  late with m < 2^(j/4): {(np.log2(mval[late].astype(float))<j/4).mean():.3f}", flush=True)
