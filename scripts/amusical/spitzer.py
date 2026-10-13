# Closed form for the orbit-minimum density via Spitzer / Sparre Andersen + Haar duality.
#   p_f = exp(-sum_k P(S_k <= 0)/k),  S_k forward log-walk  (O_k ~ Bin(k,1/2) odd steps)
#   p_b = exp(-sum_k P(B_k <= 0)/k),  B_k backward log-walk (b_k ~ Bin(k,2/3) x4/3 steps)
#   duality: P(B_k <= 0) = E[e^{-S_k}; S_k > 0], so p_f p_b = exp(-sum_k E[min(1, e^{-S_k})]/k).
from math import log, exp, comb, lgamma
L2, L3 = log(2), log(3)
def Sk(k, o): return k * L3 - (k + o) * L2            # forward: (3/2)^(k-o) (3/4)^o
def binom_pmf(k, j, p): return exp(lgamma(k+1)-lgamma(j+1)-lgamma(k-j+1) + j*log(p) + (k-j)*log(1-p))
K = 4000
sf = sb = sd = 0.0
for k in range(1, K + 1):
    pf = sum(binom_pmf(k, o, .5) for o in range(k + 1) if Sk(k, o) <= 0)
    # backward: b steps x4/3 (prob 2/3), k-b steps x2/3: B_k = (k+b) ln2 - k ln3
    pb = sum(binom_pmf(k, b, 2/3) for b in range(k + 1) if (k + b) * L2 - k * L3 <= 0)
    dual = sum(binom_pmf(k, o, .5) * (1.0 if Sk(k, o) <= 0 else exp(-Sk(k, o))) for o in range(k + 1))
    sf += pf / k; sb += pb / k; sd += dual / k
print(f"K={K}: p_f={exp(-sf):.6f} p_b={exp(-sb):.6f} product={exp(-sf-sb):.6f} dual-form={exp(-sd):.6f}")
