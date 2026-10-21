#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# The beyond-Terras parity walk: P_j(s) = sum_{r<s} (-1)^{T^j r}, s = 0..2^j.  Endpoint = E_j.
# Diffusive?  Block-increment variance over blocks of length 2^i vs 2^i; max excursion; increment kurtosis.
import numpy as np, sys
j=int(sys.argv[1]); CH=2**22; signs=np.empty(2**j, dtype=np.int8)
for start in range(0, 2**j, CH):
    n=min(CH, 2**j-start); y=np.arange(start, start+n, dtype=np.int64)
    for _ in range(j): odd=(y&1).astype(bool); y=np.where(odd,(3*y+1)>>1,y>>1)
    signs[start:start+n]=1-2*(y&1)
P=np.concatenate([[0],np.cumsum(signs, dtype=np.int64)])
print(f"j={j} E_j={P[-1]} max P={P.max()} at s/2^j={P.argmax()/2**j:.3f}  min P={P.min()} at {P.argmin()/2**j:.3f}  max|P|/2^(j/2)={np.abs(P).max()/2**(j/2):.2f}  (BM: E max|B| on [0,1] ~ 1.25 sd)")
print(" block increments over blocks of length 2^i: var/2^i (diffusive = const), mean/2^(i/2), kurtosis (Gauss 3), lag-1 autocorr")
for i in range(6, j-1, 2):
    inc=np.diff(P[::2**i]).astype(float); v=inc.var(); m=inc.mean()
    k=((inc-m)**4).mean()/v**2; ac=np.corrcoef(inc[:-1],inc[1:])[0,1]
    print(f"  i={i:2d} n={len(inc):8d} var/2^i={v/2**i:.3f} mean/2^(i/2)={m/2**(i/2):+.4f} kurt={k:.2f} ac1={ac:+.3f}")
# fraction of the walk spent positive
print(f" fraction of s with P_j(s)>0: {(P>0).mean():.3f}; zero crossings: {int((np.sign(P[1:])*np.sign(P[:-1])<0).sum())}")
