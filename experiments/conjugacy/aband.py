#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
# Decompose E_j by a = number of odd steps, and tabulate (nu mod 8, a mod 2) at depth j.
import numpy as np, sys, time
J0=int(sys.argv[1]); J1=int(sys.argv[2]); CH=2**22
for j in range(J0, J1+1):
    t0=time.time(); Ea=np.zeros(j+1, dtype=np.int64); Na=np.zeros(j+1, dtype=np.int64)
    joint=np.zeros((8,2), dtype=np.int64)
    for start in range(0, 2**j, CH):
        n=min(CH, 2**j-start)
        y = np.arange(start, start+n, dtype=np.int64); a = np.zeros(n, dtype=np.int64)
        for _ in range(j):
            odd = (y & 1).astype(bool); a += odd; y = np.where(odd, (3*y+1)>>1, y>>1)
        s = 1-2*(y&1)
        Ea += np.bincount(a, weights=s, minlength=j+1).astype(np.int64)
        Na += np.bincount(a, minlength=j+1)
        joint += np.bincount((y&7)*2+(a&1), minlength=16).reshape(8,2)
    E=int(Ea.sum()); print(f"\nj={j} E={E} E/2^(j/2)={E/2**(j/2):.3f} ({time.time()-t0:.0f}s)")
    print(" a   N_a        E_{j,a}   E/sqrt(N_a)")
    for a in range(j+1):
        if Na[a]>0: print(f"{a:3d} {Na[a]:10d} {Ea[a]:9d}  {Ea[a]/np.sqrt(Na[a]):7.2f}")
    print(" joint (nu mod 8, a mod 2) deviation from 2^j/16:")
    dev = joint - 2**j/16
    for c in range(8): print(f"  nu={c}: a even {dev[c,0]:+9.0f}  a odd {dev[c,1]:+9.0f}")
    print(f" E_(j+1) via (3.2) = 2*[n(0 mod 4,even)-n(2 mod 4,even)+n(1 mod 4,odd)-n(3 mod 4,odd)] = {2*(joint[0,0]+joint[4,0]-joint[2,0]-joint[6,0]+joint[1,1]+joint[5,1]-joint[3,1]-joint[7,1])}")
