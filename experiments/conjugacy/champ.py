#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Collatz-Champernowne sequence C_C: concatenate the first C*size(n) parity letters of n (n = 1,2,...).
# Block-frequency deviations for L = 1..8, the frequency of '11', and the fraction of letters inside cycle tails.
import numpy as np, sys
C=int(sys.argv[1]); M=int(sys.argv[2])  # letters
letters=np.empty(M, dtype=np.uint8); pos=0; n=0; tail=0
while pos<M:
    n+=1; k=n.bit_length(); L=C*k; y=n; reached=None
    for t in range(L):
        if pos+t>=M: break
        letters[pos+t]=y&1
        if reached is None and y==1: reached=t
        y=(3*y+1)>>1 if y&1 else y>>1
    if reached is not None: tail+=max(0, min(L, M-pos)-reached)
    pos+=L
letters=letters[:M]
print(f"C={C} M={M} last n={n} (size {n.bit_length()}); cycle-tail letters: {tail/M:.3%}")
for L in range(1,9):
    v=np.zeros(M-L+1, dtype=np.int64)
    for i in range(L): v=v*2+letters[i:M-L+1+i]
    cnt=np.bincount(v, minlength=2**L).astype(float); exp=(M-L+1)/2**L
    dev=np.abs(cnt/exp-1).max()
    extra=f"  f(11)={cnt[3]/(M-L+1):.4f} f(00)={cnt[0]/(M-L+1):.4f} f(01)={cnt[1]/(M-L+1):.4f}" if L==2 else ""
    print(f" L={L} max rel dev={dev:.4f} (iid expectation ~{np.sqrt(2**L/(M-L+1))*2.5:.4f}){extra}")
