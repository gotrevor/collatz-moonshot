#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Parity recursion for the coalescence density at even distance.
# For r < 2^j and distance 2d: r even -> (r/2, r/2 + d), uniform starts < 2^{j-1}: exactly coal_{j-1}(d).
#                              r odd  -> (T r, T r + 3d) with T r = (3r+1)/2 on the odd-image set.
# So coal_j(2d) = 1/2 coal_{j-1}(d) + 1/2 coalOdd_{j-1}(3d), exactly, where coalOdd uses the odd-image starts.
# Check (a) the exact identity, (b) how far coalOdd_{j-1}(3d) is from the uniform coal_{j-1}(3d).
import numpy as np, sys
jmax=int(sys.argv[1]) if len(sys.argv)>1 else 20
def T(a): return np.where(a&1==1,(3*a+1)>>1,a>>1)
def coal_from(a, d, steps):
    b=a+d; m=np.zeros(a.shape,bool)
    for _ in range(steps):
        m|=(a==b); a=T(a); b=T(b)
    m|=(a==b); return float(m.mean())
def coal(j,d): return coal_from(np.arange(2**j,dtype=np.int64), d, j)
def coal_odd_image(j,d):   # starts T r for odd r < 2^{j+1}, merging within j steps
    r=np.arange(1,2**(j+1),2,dtype=np.int64); return coal_from(T(r), d, j)
print("j   2d   coal_j(2d)   exact: (coal_{j-1}(d)+coalOdd_{j-1}(3d))/2   approx: (coal_{j-1}(d)+coal_{j-1}(3d))/2   coalOdd_{j-1}(3d)  coal_{j-1}(3d)")
for j in range(14, jmax+1, 2):
    for d in (1,2,3,4):
        lhs=coal(j,2*d); c1=coal(j-1,d); c3=coal(j-1,3*d); c3o=coal_odd_image(j-1,3*d)
        print(f"{j:2d}  {2*d:3d}   {lhs:.4f}       {(c1+c3o)/2:.4f}                              {(c1+c3)/2:.4f}                         {c3o:.4f}          {c3:.4f}", flush=True)
