#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# At the first merge step k of (s, s+D), compare the odd-step counts a_k(s), a_k(s+D).
# If a = a' the merge is a residue-class property (Terras: T^k s = (3^a s + c(v))/2^k, c depends on s mod 2^k only),
# so the coalescence density is invariant under any map that permutes residues mod 2^j; a != a' merges are
# affine coincidences (at most one s per residue class).  Report the split, uniform starts s < 2^j.
import numpy as np, sys
j=int(sys.argv[1])
def T(a): return np.where(a&1==1,(3*a+1)>>1,a>>1)
for D in (1,2,3,4,6,9,12):
    N=2**j; a=np.arange(N,dtype=np.int64); b=a+D
    ca=np.zeros(N,np.int64); cb=np.zeros(N,np.int64); done=np.zeros(N,bool); same=0; diff=0
    for k in range(1,j+1):
        ca+=a&1; cb+=b&1; a=T(a); b=T(b)
        m=(a==b)&~done
        same+=int(((ca==cb)&m).sum()); diff+=int(((ca!=cb)&m).sum()); done|=m
    tot=same+diff
    print(f"j={j} D={D:2d}: merges {tot:7d} ({tot/N:.4f})  equal odd-counts {same/tot:.4f}  unequal {diff/tot:.4f}  (unequal/N = {diff/N:.5f})", flush=True)
