#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Decompose E_j = sum_{r<2^j} (-1)^{T^j r} into the 3-adic residue term and the wrap term.
m = T^j(r) = nu + 3^a k, nu = m mod 3^a in [0,3^a), a = #odd steps, k in {0,1}.
Also: accumulation profile of the running sum over r (where does the excess sit?)."""
import numpy as np, sys
def run(j):
    r = np.arange(2**j, dtype=np.uint64); m = r.copy(); a = np.zeros(2**j, dtype=np.int64)
    for _ in range(j):
        odd = (m & 1).astype(bool); a += odd; m = np.where(odd, (3*m+1)>>1, m>>1)
    p3 = (3**a.astype(object))  # python ints for exactness up to 3^24 fits int64 anyway
    p3 = np.array([3**int(x) for x in range(j+1)], dtype=np.uint64)[a]
    nu = m % p3; k = (m - nu)//p3
    s_m = 1 - 2*(m & 1).astype(np.int64); s_nu = 1 - 2*(nu & 1).astype(np.int64)
    E = s_m.sum(); A = s_nu.sum(); B = s_nu[k==1].sum(); nwrap = int((k==1).sum()); kmax = int(k.max())
    # accumulation profile: running sum at r = 2^i
    prof = [int(s_m[:2**i].sum()) for i in range(0, j+1)]
    # by a (number of odd steps): E restricted to each a
    byA = [(int(x), int(s_m[a==x].sum()), int((a==x).sum())) for x in range(j+1)]
    return E, A, B, nwrap, kmax, prof, byA
for j in range(8, int(sys.argv[1])+1):
    E, A, B, nwrap, kmax, prof, byA = run(j)
    print(f"j={j:2d} E={E:6d} A(sum(-1)^nu)={A:6d} B(wrap part)={B:6d} E-(A-2B)={E-(A-2*B)} nwrap={nwrap} ({nwrap/2**j:.4f}, (3/4)^j={0.75**j:.4f}) kmax={kmax}")
    print("   running sum at r<2^i:", prof)
    print("   by a: (a, E_a, count):", [t for t in byA if t[2]>0 and abs(t[1])>=max(2,0)][:j+1])
