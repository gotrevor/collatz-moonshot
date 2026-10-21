#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Per-stage test of ShortIntervalMixing: for k-bit n (stage k), the beyond-range letters t in [k, C k).
# Reports, per stage, the max relative deviation of L-block frequencies among beyond-range positions,
# the single-letter bias per position band, and the fraction of orbits that reached 1 within C k steps.
import numpy as np, sys
C=int(sys.argv[1]); K0=int(sys.argv[2]); K1=int(sys.argv[3])
for k in range(K0, K1+1):
    n=np.arange(2**(k-1), 2**k, dtype=np.int64); T=C*k
    W=np.empty((len(n), T), dtype=np.uint8); y=n.copy(); reached=np.full(len(n), T, dtype=np.int64)
    for t in range(T):
        W[:,t]=y&1; hit=(y==1)&(reached==T); reached[hit]=t
        y=np.where(y&1==1, (3*y+1)>>1, y>>1)
    beyond=W[:, k:]            # letters at positions k..Ck-1 (beyond the Terras range)
    frac_reached=(reached<T).mean()
    out=[f"C={C} k={k:2d} words={len(n)} reached1 within Ck: {frac_reached:.3%}"]
    # single-letter bias by position band
    for (a,b) in [(k, int(1.5*k)), (int(1.5*k), 2*k), (2*k, 3*k), (3*k, T)]:
        if a<b and b<=T:
            m=W[:, a:b].mean(); out.append(f"  bias[{a},{b})={2*m-1:+.4f}")
    # block deviations over beyond-range positions, blocks fully inside beyond zone
    for L in (2,3,4):
        v=np.zeros((len(n), beyond.shape[1]-L+1), dtype=np.int64)
        for i in range(L): v=v*2+beyond[:, i:beyond.shape[1]-L+1+i]
        cnt=np.bincount(v.ravel(), minlength=2**L).astype(float); N=v.size
        dev=np.abs(cnt/(N/2**L)-1).max(); noise=np.sqrt(2**L/N)
        out.append(f"  L={L} maxdev={dev:.4f} (noise {noise:.4f}, ratio {dev/noise:5.1f})" + (f" f11={cnt[3]/N:.4f}" if L==2 else ""))
    print(" |".join(out), flush=True)
