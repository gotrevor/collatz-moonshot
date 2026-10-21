#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Among pairs (r, r+d), r < 2^j, not merged by step j: split by the step at which they merge (j+1, j+2, ..., never within j+E)
# and report the sign product at step j in each class.  Pairs merging at exactly j+1 must have product -1 (theorem).
import numpy as np, sys
j=int(sys.argv[1]); E=int(sys.argv[2]); N=2**j
for d in (1,2,4,16):
    a=np.arange(N, dtype=np.int64); b=a+d; merged=np.zeros(N, dtype=bool)
    for k in range(j):
        merged |= (a==b); a=np.where(a&1==1,(3*a+1)>>1,a>>1); b=np.where(b&1==1,(3*b+1)>>1,b>>1)
    merged |= (a==b); prod=(1-2*(a&1))*(1-2*(b&1))
    nc=~merged; mt=np.full(N, -1, dtype=np.int64)   # merge time beyond j
    aa=a.copy(); bb=b.copy()
    for e in range(1,E+1):
        aa=np.where(aa&1==1,(3*aa+1)>>1,aa>>1); bb=np.where(bb&1==1,(3*bb+1)>>1,bb>>1)
        newly=(aa==bb)&(mt<0)&nc; mt[newly]=e
    out=[f"d={d}: nonmerged={nc.mean():.4f} R_nc={prod[nc].mean():+.4f} |"]
    for e in range(1,6):
        sel=nc&(mt==e)
        if sel.any(): out.append(f" merge@j+{e}: frac={sel.mean():.4f} prod={prod[sel].mean():+.3f}")
    sel=nc&(mt>5); out.append(f" merge@>j+5(<=j+{E}): frac={sel.mean():.4f} prod={prod[sel].mean():+.3f}")
    sel=nc&(mt<0); out.append(f" nomerge by j+{E}: frac={sel.mean():.4f} prod={prod[sel].mean():+.4f}")
    print("".join(out), flush=True)
