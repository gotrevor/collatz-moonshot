#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Walsh spectrum of the beyond-Terras letter in the parity-word picture.
# Terras: r mod 2^j <-> parity word v = (v_1..v_j), v_i = parity of T^{i-1} r.  Let g(v) = (-1)^{T^j r} be the
# (j+1)-th letter.  Walsh coefficient at S subset of {1..j}: ghat(S) = 2^-j sum_v g(v) (-1)^{sum_{i in S} v_i}
# = correlation of the next letter with the XOR of the letters in S.  ghat(empty) = E_j / 2^j.  Parseval:
# sum ghat^2 = 1.  Report energy by degree |S| and by the position of the most recent letter in S
# (max i; i = j is the letter just before), i.e. how far back and how deep the dependence reaches.
import numpy as np, sys
def fwht(a):
    a=a.astype(np.float64).copy(); h=1; n=len(a)
    while h<n:
        a=a.reshape(-1,2*h); x=a[:,:h].copy(); y=a[:,h:].copy(); a[:,:h]=x+y; a[:,h:]=x-y; a=a.reshape(n); h*=2
    return a
for j in [int(x) for x in sys.argv[1:]]:
    N=2**j; r=np.arange(N,dtype=np.int64); idx=np.zeros(N,np.int64); a=r.copy()
    for i in range(j):
        idx|=((a&1)<<i); a=np.where(a&1==1,(3*a+1)>>1,a>>1)
    g=1-2*(a&1)                       # (j+1)-th letter sign, as a function of r
    assert len(np.unique(idx))==N     # Terras bijection check
    G=np.zeros(N,np.float64); G[idx]=g  # g as a function of the parity word (bit i-1 <-> letter i)
    gh=fwht(G)/N; E=int(g.sum()); assert abs(gh[0]-E/N)<1e-12
    S=np.arange(N); deg=np.array([bin(x).count('1') for x in range(N)]); 
    top=np.where(S>0, np.floor(np.log2(np.maximum(S,1))).astype(int)+1, 0)   # most recent letter position in S
    en=gh**2; tot=en.sum()
    bydeg=[en[deg==d].sum()/tot for d in range(0,min(j,8)+1)]
    bytop=[en[top==t].sum()/tot for t in range(0,j+1)]
    rec=[en[top>=j-m].sum()/tot for m in (0,1,2,3,5,7)]  # energy on sets whose most recent letter is among the last m+1
    print(f"j={j}: E_j/2^j={E/N:+.5f} (E_j={E}); Parseval={tot:.6f}")
    print(f"   energy by degree 0..{min(j,8)}: "+" ".join(f"{x:.4f}" for x in bydeg)+f"  (deg>{min(j,8)}: {1-sum(bydeg):.4f})")
    print(f"   energy by most-recent letter position 1..{j}: "+" ".join(f"{x:.3f}" for x in bytop[1:]))
    print(f"   energy on S within the last 1/2/3/4/6/8 letters: "+" ".join(f"{x:.3f}" for x in rec))
    big=np.argsort(-en)[:8]
    print("   top coefficients: "+", ".join(f"S={{{','.join(str(i+1) for i in range(j) if (s>>i)&1)}}}:{gh[s]:+.4f}" for s in big), flush=True)
