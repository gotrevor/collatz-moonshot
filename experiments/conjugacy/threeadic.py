#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""3-adic structure of the signed parity measure mu_m = sum_{y<2^m} (-1)^{T^m y} delta_y.
Checks: (1) exact recursion E_m = 2 E_{m-1} - 2 G_{m-1}(c_m), c_m = (2 - 2^{m-1}) mod 3;
(2) class biases beta_m(c) = mean (-1)^{T^m y} over y = c mod 3, vs b_m;
(3) |mu_hat_m(1/3)| and |mu_hat_m(1/9)| vs E_m and 2^{m/2};
(4) exact E_j for j up to J (chunked)."""
import numpy as np, sys, cmath
J = int(sys.argv[1])
CH = 2**22
def signs_and_vals(j):
    """yield (y, sign) chunks for y < 2^j."""
    for start in range(0, 2**j, CH):
        y = np.arange(start, min(start+CH, 2**j), dtype=np.int64); m = y.copy()
        for _ in range(j):
            odd = (m & 1).astype(bool); m = np.where(odd, (3*m+1)>>1, m>>1)
        yield y, (1 - 2*(m & 1))
prevE=None; prevG=None
for j in range(1, J+1):
    E=0; G=np.zeros(3, dtype=np.int64); F3=0j; F9=0j; cnt3=np.zeros(3,dtype=np.int64)
    for y, s in signs_and_vals(j):
        E += int(s.sum())
        for c in range(3):
            msk = (y % 3 == c); G[c] += int(s[msk].sum()); cnt3[c] += int(msk.sum())
        F3 += complex((s*np.cos(2*np.pi*y/3)).sum(), (s*np.sin(2*np.pi*y/3)).sum())
        F9 += complex((s*np.cos(2*np.pi*y/9)).sum(), (s*np.sin(2*np.pi*y/9)).sum())
    c_m = (2 - 2**(j-1)) % 3
    rec = (2*(prevE - prevG[c_m]) if prevE is not None else None)
    beta = G / np.maximum(cnt3,1)
    print(f"j={j:2d} E={E:7d} rec={rec} ok={rec==E if rec is not None else '-'}  b={E/2**j:+.2e}  beta(c)={beta[0]:+.2e},{beta[1]:+.2e},{beta[2]:+.2e}  |F(1/3)|/2^(j/2)={abs(F3)/2**(j/2):.2f} |F(1/9)|/2^(j/2)={abs(F9)/2**(j/2):.2f}  E/2^(j/2)={E/2**(j/2):.2f}  (4/3)^j/2^(j/2)={(4/3)**j/2**(j/2):.3f}", flush=True)
    prevE, prevG = E, G
