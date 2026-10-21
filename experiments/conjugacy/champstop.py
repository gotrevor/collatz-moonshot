#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# The stop-at-1 Collatz-Champernowne sequence: concatenate the parity letters of n until the orbit first hits 1.
import numpy as np, sys
M=int(sys.argv[1]); letters=np.empty(M, dtype=np.uint8); pos=0; n=0; lens=[]
while pos<M:
    n+=1; y=n; t=0
    while y!=1 and pos+t<M:
        letters[pos+t]=y&1; y=(3*y+1)>>1 if y&1 else y>>1; t+=1
    lens.append(t); pos+=max(t,1) if t>0 else 0
    if t==0: pass
letters=letters[:M]; lens=np.array(lens)
print(f"stop-at-1: M={M} last n={n} (size {n.bit_length()}), mean word length/size(n) = {lens[1:].mean()/np.log2(np.arange(2,n+1)).mean():.2f} (C* = 4.82)")
for L in range(1,9):
    v=np.zeros(M-L+1, dtype=np.int64)
    for i in range(L): v=v*2+letters[i:M-L+1+i]
    cnt=np.bincount(v, minlength=2**L).astype(float); exp=(M-L+1)/2**L
    dev=np.abs(cnt/exp-1).max()
    extra=f"  f(11)={cnt[3]/(M-L+1):.4f} f(00)={cnt[0]/(M-L+1):.4f} f(01)={cnt[1]/(M-L+1):.4f}" if L==2 else ""
    print(f" L={L} max rel dev={dev:.4f} (iid ~{np.sqrt(2**L/(M-L+1))*2.5:.4f}){extra}")
