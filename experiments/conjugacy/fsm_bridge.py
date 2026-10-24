#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""3-adic bridge for BiasDecays: E_j = sum_a sum_{r: a(r)=a} (-1)^{T^j r}, and T^j(r) < 3^a is the
least residue of a Syracuse-type variable mod 3^a.  Check (i) E_j against the frozen table, and
(ii) the reduction |sum_{a(r)=a} (-1)^{T^j r}| / #a  <=  osc_{m,a}(mu_{j,a}) + 3^{m-a}  for every m < a,
with osc_{m,n}(mu) = sum_{Y mod 3^n} |mu(Y) - 3^{m-n} mu(Y mod 3^m)|  (Tao's oscillation)."""
import sys, numpy as np
KNOWN = {16: 362, 18: 570, 20: 1042, 22: 4206}
def run(j):
    r = np.arange(2**j, dtype=np.int64); x = r.copy(); a = np.zeros_like(r)
    for _ in range(j):
        odd = (x & 1).astype(bool)
        x = np.where(odd, (3*x + 1) >> 1, x >> 1); a += odd
    E = int(np.sum(1 - 2*(x & 1)))
    assert np.all(x < 3**a), "T^j(r) < 3^a fails"
    out = []
    for aa in range(j+1):
        sel = x[a == aa]; cnt = sel.size
        if cnt < 2**(j-6): continue                      # only the bulk of the binomial
        bias = abs(int(np.sum(1 - 2*(sel & 1)))) / cnt
        vals, mult = np.unique(sel, return_counts=True); mu = mult / cnt
        best = (9.0, None)
        for m in range(1, aa):
            c = vals % 3**m
            cls, inv, ncls = np.unique(c, return_inverse=True, return_counts=True)
            mum = np.bincount(inv, weights=mu)            # mu mod 3^m
            lam = mum[inv] * 3.0**(m-aa)
            osc = np.sum(np.abs(mu - lam)) + np.sum(mum * (1 - ncls * 3.0**(m-aa)))  # support + empty lifts
            bnd = osc + 3.0**(m-aa)
            assert bias <= bnd + 1e-12, (j, aa, m, bias, bnd)
            if bnd < best[0]: best = (bnd, m, osc)
        out.append((aa, cnt, bias, best))
    return E, out
for j in map(int, sys.argv[1:]):
    E, out = run(j)
    print(f"j={j}  E_j={E}" + (f"  (frozen {KNOWN[j]}: {'OK' if KNOWN[j]==E else 'MISMATCH'})" if j in KNOWN else ""))
    for aa, cnt, bias, (bnd, m, osc) in out:
        print(f"   a={aa:2d} n={cnt:8d}  |bias_a|={bias:.2e}  best m={m:2d}  osc={osc:.3f}  bound={bnd:.3f}")
