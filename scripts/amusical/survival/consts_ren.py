"""Ren's re-derivation of the survival agent's constants (2026-10-13).
Forward walk: slope product after k steps with o odd steps is 3^k / 2^(k+o), o ~ Bin(k, 1/2).
  p_f = exp(-sum_k P(2^(k+o) > 3^k)/k).
Backward walk: steps 2/3 (prob 1/3), 4/3 (prob 2/3); o = # of 4/3 steps; product 2^(k+o)/3^k.
  p_b = exp(-sum_k P(2^(k+o) < 3^k)/k), weight C(k,o) 2^o / 3^k.
No ties (2^a != 3^b).  The threshold o*(k) = least o with 2^(k+o) > 3^k is found exactly."""
from math import lgamma, log, exp, floor, log2
K = 6000
TH = log2(3)
sf = sb = 0.0
for k in range(1, K + 1):
    o = max(0, floor(k * (TH - 1)))
    t3 = 3 ** k
    while o > 0 and 2 ** (k + o - 1) > t3: o -= 1
    while 2 ** (k + o) <= t3: o += 1          # exact: o is the least with 2^(k+o) > 3^k
    lk = lgamma(k + 1)
    pf = sum(exp(lk - lgamma(j + 1) - lgamma(k - j + 1) - k * log(2)) for j in range(o, k + 1))
    pb = sum(exp(lk - lgamma(j + 1) - lgamma(k - j + 1) + j * log(2) - k * log(3)) for j in range(0, o))
    sf += pf / k; sb += pb / k
p_f, p_b = exp(-sf), exp(-sb)
print(f"K={K}: p_f={p_f:.12f}  p_b={p_b:.12f}  p_f*p_b={p_f*p_b:.10f}")
for th in (0.0, 0.3, 0.4951, 0.9):
    l = (1/3)*(3/2)**th + (2/3)*(3/4)**th
    r = 0.5*(2/3)**(1-th) + 0.5*(4/3)**(1-th)
    print(f"tilt theta={th}: lhs-rhs={l-r:.2e}")
rho = min(0.5*(3/2)**(-t/10000) + 0.5*(3/4)**(-t/10000) for t in range(0, 10001))
print("rho =", round(rho, 6))
