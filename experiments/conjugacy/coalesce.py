#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Coalescence vs correlation: coal_j(d) = fraction of r < 2^j with T^k r = T^k (r+d) for some k <= j;
# R_j(d) = correlation of the j-th letter signs of r and r+d over r < 2^j (window form).
# Also the correlation restricted to NON-coalesced pairs (should be ~0 if coalescence is the whole story).
import numpy as np, sys
j=int(sys.argv[1]); N=2**j
def orbit_signs_and_coal(d):
    a=np.arange(N, dtype=np.int64); b=a+d; coal=np.zeros(N, dtype=bool)
    for k in range(j):
        coal |= (a==b)
        a=np.where(a&1==1,(3*a+1)>>1,a>>1); b=np.where(b&1==1,(3*b+1)>>1,b>>1)
    coal |= (a==b)
    sa=1-2*(a&1); sb=1-2*(b&1)
    return sa, sb, coal
print(f"j={j}:   d   coal_j(d)   R_j(d)   R among non-coalesced   coal+(1-coal)*R_nc")
for d in [1,2,3,4,5,6,7,8,12,16,32,64,256,1024]:
    sa,sb,coal=orbit_signs_and_coal(d); R=float((sa*sb).mean()); c=float(coal.mean())
    nc=~coal; Rnc=float((sa[nc]*sb[nc]).mean()) if nc.any() else float('nan')
    print(f"      {d:5d}   {c:.4f}      {R:+.4f}   {Rnc:+.4f}                 {c+(1-c)*Rnc:+.4f}")
