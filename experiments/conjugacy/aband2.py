#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Per-odd-count-band bias for the map T(n) = n/2 | (q n + c)/2, plus (a, last-one-position) split.
import numpy as np, sys, time
q=int(sys.argv[1]); c=int(sys.argv[2]); J0=int(sys.argv[3]); J1=int(sys.argv[4]); DSPLIT=len(sys.argv)>5
CH=2**22
for j in range(J0, J1+1):
    t0=time.time(); Ea=np.zeros(j+1); Na=np.zeros(j+1)
    if DSPLIT: Ead=np.zeros((j+1,j+1)); Nad=np.zeros((j+1,j+1))
    for start in range(0, 2**j, CH):
        n=min(CH, 2**j-start)
        y=np.arange(start, start+n, dtype=np.int64); a=np.zeros(n, dtype=np.int64); last=np.full(n, -1, dtype=np.int64)
        for i in range(j):
            odd=(y&1).astype(bool); a+=odd; last=np.where(odd, i, last); y=np.where(odd, (q*y+c)>>1, y>>1)
        s=1-2*(y&1)
        Ea+=np.bincount(a, weights=s, minlength=j+1); Na+=np.bincount(a, minlength=j+1)
        if DSPLIT:
            idx=a*(j+1)+np.maximum(last,0)
            Ead+=np.bincount(idx, weights=s, minlength=(j+1)**2).reshape(j+1,j+1)
            Nad+=np.bincount(idx, minlength=(j+1)**2).reshape(j+1,j+1)
    E=int(Ea.sum()); inner=[(Ea[a]/np.sqrt(Na[a])) for a in range(2,j-1)]
    pos=sum(1 for x in inner if x>0); neg=sum(1 for x in inner if x<0)
    print(f"{q}x+{c} j={j} E={E} E/2^(j/2)={E/2**(j/2):+.3f} bands(a=2..j-2) +{pos} -{neg} mean={np.mean(inner):+.2f} sd={np.std(inner):.2f} ({time.time()-t0:.0f}s)", flush=True)
    if DSPLIT:
        print(" (a, d_last) cells with N>=64: normalized E/sqrt(N); rows a, cols d")
        vals=[]
        for a in range(2,j-1):
            row=[]
            for d in range(j):
                if Nad[a,d]>=64: v=Ead[a,d]/np.sqrt(Nad[a,d]); vals.append(v); row.append(f"{v:+.1f}")
                else: row.append("  . ")
            print(f" a={a:2d} "+" ".join(row))
        vals=np.array(vals); print(f" cells: n={len(vals)} +{(vals>0).sum()} -{(vals<0).sum()} mean={vals.mean():+.2f} sd={vals.std():.2f}")
