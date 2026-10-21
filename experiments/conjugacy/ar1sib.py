#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# E_j for qx+c maps, j = 6..24, and the lag-1 structure of the normalized bias b~_j = E_j/2^(j/2):
# the uniform-class null predicts b~_m = rho0 b~_{m-1} + eta with rho0 = (1+1/q)/sqrt2.
import numpy as np, sys
CH=2**22
def E(q,c,j):
    tot=0
    for start in range(0,2**j,CH):
        n=min(CH,2**j-start); y=np.arange(start,start+n,dtype=np.int64)
        for _ in range(j):
            odd=(y&1).astype(bool); y=np.where(odd,(q*y+c)>>1,y>>1)
        tot+=int((1-2*(y&1)).sum())
    return tot
for (q,c) in [(3,1),(3,5),(3,7),(3,-1),(5,1),(5,3),(7,1),(7,3)]:
    js=list(range(6,25)); Es=[E(q,c,j) for j in js]; b=np.array(Es)/2.0**(np.array(js)/2)
    rho0=(1+1/q)/np.sqrt(2)
    x=b[4:-1]; y=b[5:]  # fit from j>=11
    rho=(x*y).sum()/(x*x).sum(); eta=y-rho0*x
    sgn=np.sign(Es); flips=int((sgn[4:-1]*sgn[5:]<0).sum())
    print(f"{q}x+{c:+d}: rho0={rho0:.3f} rho_hat={rho:.3f} eta mean={eta.mean():+.3f} sd={eta.std():.3f} sign flips(j>=10)={flips}  E_j(j=10..24)={Es[4:]}")
