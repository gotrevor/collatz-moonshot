#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Family-wide test of the innovation drift: eta_m = (E_m - (1+1/q) E_{m-1}) / 2^(m/2) for many qx+c maps, j = 8..J.
import numpy as np, sys
J=int(sys.argv[1]); CH=2**22
def E(q,c,j):
    tot=0
    for start in range(0,2**j,CH):
        n=min(CH,2**j-start); y=np.arange(start,start+n,dtype=np.int64)
        for _ in range(j):
            odd=(y&1).astype(bool); y=np.where(odd,(q*y+c)>>1,y>>1)
        tot+=int((1-2*(y&1)).sum())
    return tot
maps=[(3,1),(3,5),(3,7),(3,11),(3,13),(3,17),(5,1),(5,3),(5,7),(5,9),(7,1),(7,3),(7,5),(9,1),(11,1),(13,1)]
allm=[]
for (q,c) in maps:
    js=list(range(8,J+1)); Es=np.array([E(q,c,j) for j in js],dtype=float)
    eta=(Es[1:]-(1+1/q)*Es[:-1])/2.0**(np.array(js[1:])/2)
    e=eta[2:]  # from j>=11
    t=e.mean()/(e.std(ddof=1)/np.sqrt(len(e)))
    allm.append(e.mean()); print(f"{q:2d}x+{c:2d}: eta mean={e.mean():+.3f} sd={e.std(ddof=1):.3f} n={len(e)} t={t:+.2f}   E_J={int(Es[-1])} E_J/2^(J/2)={Es[-1]/2**(J/2):+.2f}", flush=True)
allm=np.array(allm); print(f"across {len(maps)} maps: mean of eta-means={allm.mean():+.3f}, sd={allm.std(ddof=1):.3f}, positive {int((allm>0).sum())}/{len(maps)}, t={allm.mean()/(allm.std(ddof=1)/np.sqrt(len(allm))):+.2f}")
