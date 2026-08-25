#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""Exact-ish constants for sep_two_three_of_gelfond_measure under a Rhin-type bound
   |m log2 - k log3| > H^{-E},  H = max(m,k) = m,  3^k < 2^m < 2*3^k."""
from mpmath import mp, mpf, log, ceil
mp.dps = 40
d = log(3)/log(2)          # delta

def min_C(E, K0):
    # need E*log(K0*d+1) <= C*log(K0)  (worst at k=K0, decreasing in k)
    return E*log(K0*d+1)/log(K0)

def min_k_for_crossover(C):
    # least K1 with k^(3C) <= 2^k for all k >= K1  (exact integer test)
    k = 2
    last_fail = 1
    while k < 200000:
        if k**(3*C) <= 2**k:
            # check it stays true (it does, monotone past crossing) - verify next 50
            if all(j**(3*C) <= 2**j for j in range(k, k+50)):
                return k
        else:
            last_fail = k
        k += 1
    return None

print(f"delta = {d}")
for E in (mpf('13.3'), mpf('7.616')):
    print(f"\n=== E = {E} ===")
    for K0 in (130, 200, 250, 300, 387, 400, 500):
        print(f"  K0={K0:4d}: minimal real C = {min_C(E,K0):.4f} -> C = {int(ceil(min_C(E,K0)))}")

print()
for C in (6, 9, 10, 14, 15, 16):
    print(f"C={C:3d}: k^{3*C} <= 2^k first holds (and persists) at k = {min_k_for_crossover(C)}")

# one-circuit (Steiner): contradiction when 2^k - 1 >= (k+l)^E, k+l = ceil(k*delta)
print("\n=== one-circuit: least k with 2^k - 1 >= (ceil(k*delta))^13.3 ===")
E = mpf('13.3')
for k in range(80, 130):
    kl = int(ceil(k*d))
    if mpf(2)**k - 1 >= mpf(kl)**E:
        print(f"  k = {k}  (k+l ~ {kl})"); break
