#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Instrument check of the Terras reading of C_1 (block of n = its first size(n) parity letters).
# (1) Exact interior uniformity: at level k (n in [2^k, 2^(k+1))), every m-word occurs exactly 2^(k-m) times at
#     every offset i with i + m <= k.  CONTROL: the window ending on the block's last letter (i + m = k + 1) must FAIL,
#     its last letter carrying the bias -E_k.
# (2) Partial level: at N = 2^k + 2^(k-t), the count of offsets whose m-words are not balanced should be <= about t + m.
# (3) Prefix frequencies of C_1 itself, m = 1..4, n < 2^K, plus cross-boundary windows included: sup |freq - 2^-m|.
# (4) Disjunctive construction: for random words w of length j, n = r + 2^j (r = Terras residue of w) has block prefix w.
import numpy as np, sys, random
def T(a): return np.where(a&1==1,(3*a+1)>>1,a>>1)
def letters(n,L):
    out=np.zeros((len(n),L),dtype=np.int8); a=n.copy()
    for t in range(L): out[:,t]=a&1; a=T(a)
    return out
for k,m in ((12,3),(14,4),(16,4)):
    n=np.arange(2**k,2**(k+1),dtype=np.int64); W=letters(n,k+1); bad=[]
    for i in range(0,k+2-m):
        code=(W[:,i:i+m]*(2**np.arange(m))).sum(axis=1); c=np.bincount(code,minlength=2**m)
        if not (c==2**(k-m)).all(): bad.append(i)
    Ek=int((1-2*W[:,k]).sum())
    print(f"level k={k}, m={m}: unbalanced offsets {bad} (control: only i={k+1-m} expected); last-letter sum over the level = {Ek}")
    for t in (1,3,6):
        L=2**(k-t); W2=W[:L]; b=0
        for i in range(0,k+2-m):
            code=(W2[:,i:i+m]*(2**np.arange(m))).sum(axis=1); c=np.bincount(code,minlength=2**m)
            if c.max()-c.min()>2**(i+m): b+=1     # beyond the one-period edge error
        print(f"   partial level t={t}: offsets beyond one-period error {b} of {k+2-m}; bound t+m = {t+m}")
K=int(sys.argv[1]); parts=[]
for k in range(K):
    n=np.arange(2**k,2**(k+1),dtype=np.int64); parts.append(letters(n,k+1).ravel())
s=np.concatenate(parts); print(f"C_1 prefix, n < 2^{K}: {len(s)} letters")
for m in range(1,5):
    code=sum(s[i:len(s)-m+1+i].astype(np.int64)*2**i for i in range(m)); f=np.bincount(code,minlength=2**m)/len(code)
    print(f"   m={m}: sup |freq - 2^-m| = {np.abs(f-2.0**-m).max():.2e}")
random.seed(1); ok=0
for _ in range(2000):
    j=random.randint(1,24); w=[random.randint(0,1) for _ in range(j)]
    lo,hi=0,1   # build r bit by bit: letter i of r is flipped by adding 2^i
    r=0
    for i in range(j):
        a=r
        for _t in range(i): a=(3*a+1)>>1 if a&1 else a>>1
        if (a&1)!=w[i]: r+=2**i
    n=r+2**j; a=n; got=[]
    for _t in range(j): got.append(a&1); a=(3*a+1)>>1 if a&1 else a>>1
    ok+=got==w and n.bit_length()==j+1
print(f"disjunctive construction: {ok}/2000 words appear as the block prefix of n = r + 2^j")
