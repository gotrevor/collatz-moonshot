#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Sibling test for the bias: T_{q,c}(x) = x/2 (even), (q x + c)/2 (odd), c odd.
E_j(q,c) = sum_{r<2^j} (-1)^{T^j r}.  Also diagnostics for (3,1): split by nu mod 4, by small nu, by a."""
import numpy as np, sys
def E(q, c, J, diag=False):
    out=[]
    for j in range(1, J+1):
        r = np.arange(2**j, dtype=np.int64); m = r.copy(); a = np.zeros(2**j, dtype=np.int64)
        for _ in range(j):
            odd = (m & 1).astype(bool); a += odd; m = np.where(odd, (q*m+c)>>1, m>>1)
        s = 1 - 2*(m & 1)
        out.append(int(s.sum()))
        if diag and j >= 16:
            p3 = np.array([3**int(x) for x in range(j+1)], dtype=np.int64)[a]
            print(f"  j={j}: E={s.sum()}  by nu mod 4 (count,E):", [(int((m%4==k).sum()), int(s[m%4==k].sum())) for k in range(4)],
                  " nu<2^{j/2}:", int((m < 2**(j//2)).sum()), int(s[m < 2**(j//2)].sum()),
                  " nu>=3^a/2:", int((2*m >= p3).sum()), int(s[2*m>=p3].sum()),
                  " a<j/2:", int((2*a<j).sum()), int(s[2*a<j].sum()), " a>j/2:", int((2*a>j).sum()), int(s[2*a>j].sum()))
    return out
J=int(sys.argv[1])
for (q,c) in [(3,1),(3,-1),(3,5),(3,7),(3,-5),(5,1),(5,-1),(7,1),(1,1),(1,-1)]:
    e = E(q,c,J, diag=(q==3 and c==1))
    print(f"q={q} c={c:+d}: E_j =", e, "  E_j/2^(j/2) tail:", [round(x/2**(j/2),2) for j,x in enumerate(e,1)][-6:])
