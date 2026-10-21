#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Localize the sign of E_j: joint (nu mod 4, a mod 2); split by last two letters v_{j-2} v_{j-1};
3-adic cylinder mass growth S_i(m) = sum over depth-i cylinders of mu_m(c)^2."""
import numpy as np, sys
J=int(sys.argv[1])
for j in range(14, J+1, 2):
    r = np.arange(2**j, dtype=np.int64); m = r.copy(); a = np.zeros(2**j, dtype=np.int64)
    last = np.zeros(2**j, dtype=np.int64)
    for i in range(j):
        odd = (m & 1).astype(bool); a += odd
        if i >= j-2: last = 2*last + odd
        m = np.where(odd, (3*m+1)>>1, m>>1)
    s = 1 - 2*(m & 1); sc = 2**(j/2)
    print(f"j={j}: E/2^(j/2)={s.sum()/sc:+.2f}")
    tab = [[int(((m%4==c)&(a%2==p)).sum()) - 2**(j-3) for c in range(4)] for p in range(2)]
    print("   joint dev (rows a even/odd; cols nu mod 4)/2^(j/2):", [[round(x/sc,2) for x in row] for row in tab])
    print("   E split by last two letters (00,01,10,11)/2^(j/2):", [round(int(s[last==k].sum())/sc,2) for k in range(4)],
          " counts:", [int((last==k).sum()) for k in range(4)])
    # (nu mod 4) deviation within each last-two-letter class
    for k in range(4):
        msk = last==k
        print(f"      last={k:02b}: nu mod 4 dev/2^(j/2):", [round((int(((m%4==c)&msk).sum()) - msk.sum()/4)/sc,2) for c in range(4)])
    # 3-adic cylinder masses: S_i = sum_c mu(c)^2 over depth-i cylinders, normalized by 2^j
    for i in [1,2,3,5,8]:
        cyl = m*0  # placeholder
        res = r % 3**i
        masses = np.bincount(res, weights=s, minlength=3**i)
        print(f"   depth {i}: sum mu(c)^2 / 2^j = {(masses**2).sum()/2**j:.3f}  (iid-signs expectation 1.000)")
