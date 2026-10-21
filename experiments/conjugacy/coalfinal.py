#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Eventual fate of consecutive pairs (r, r+d), r < 2^J: merge before either reaches the cycle {1,2};
# both in the cycle in phase (merged there); both in the cycle in antiphase (signs opposite forever).
# Also coal_j(1) as a function of j (window r < 2^j, merge within j steps) for the convergence trend.
import numpy as np, sys
J=int(sys.argv[1]); STEPS=int(sys.argv[2])
def fate(d):
    N=2**J; a=np.arange(1,N+1,dtype=np.int64); b=a+d
    merged=np.zeros(N,bool); done=np.zeros(N,bool); anti=np.zeros(N,bool); inphase=np.zeros(N,bool)
    for k in range(STEPS):
        eq=(a==b)&~done; incyc=(a<=2)&(b<=2)&~done
        merged|=eq&~incyc; inphase|=eq&incyc; anti|=incyc&~eq
        done|=eq|incyc
        if done.all(): break
        a=np.where(a&1==1,(3*a+1)>>1,a>>1); b=np.where(b&1==1,(3*b+1)>>1,b>>1)
    print(f"d={d}: merge before cycle {merged.mean():.4f}, in-phase at cycle {inphase.mean():.4f}, antiphase {anti.mean():.4f}, undecided {(~done).mean():.4f}  -> fixed-start limit correlation = {merged.mean()+inphase.mean()-anti.mean():+.4f}", flush=True)
for d in (1,2,3,4): fate(d)
print("coal_j(1) trend (merge within j steps, r < 2^j):")
for j in range(10, J+1, 2):
    N=2**j; a=np.arange(N,dtype=np.int64); b=a+1; m=np.zeros(N,bool)
    for k in range(j):
        m|=(a==b); a=np.where(a&1==1,(3*a+1)>>1,a>>1); b=np.where(b&1==1,(3*b+1)>>1,b>>1)
    m|=(a==b); print(f"  j={j}: coal_j(1)={m.mean():.4f}", flush=True)
