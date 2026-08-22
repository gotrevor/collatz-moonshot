#!/usr/bin/env -S uv run --quiet python3
"""Two corrections and one measurement.

(1) A cycle is a NECKLACE, not a word: k words per cycle.  Redo the k<=20 tally
    in necklace terms and ask whether 0 observed is actually surprising.
(2) Only the band k = ceil(x log2 3) can host cycles with LARGE elements; the
    x/k ~ 1/2 mass predicts cycles of bounded size, killed by verification.
(3) Measure the margin in that band, and compare it to what Baker already gives.
"""
from math import comb, log2, log, ceil, exp

print("=== (1) k<=20 in NECKLACE terms ===")
tot = 0.0
for k in range(3, 21):
    for x in range(1, k):
        D = 2**k - 3**x
        if D <= 0: continue
        if k % 2 == 0 and x * 2 == k: continue   # trivial-cycle repeats
        tot += comb(k, x) / (k * D)
print(f"expected nontrivial cycles, 3<=k<=20 : {tot:.3f}")
print(f"P(Poisson = 0)                       : {exp(-tot):.3f}   <- observing 0 is unremarkable")

print("\n=== (2)+(3) the large-element band, k = ceil(x log2 3) ===")
L = log2(3)
print(f"{'x':>6} {'k':>6} {'log2 C(k,x)':>12} {'log2 D':>9} {'log2 expected':>14} {'/k':>8}")
for x in (50, 100, 200, 400, 800, 1600):
    k = ceil(x * L)
    D = 2**k - 3**x
    lc = log2(comb(k, x)); ld = log2(D)
    e = lc - ld - log2(k)
    print(f"{x:>6} {k:>6} {lc:>12.1f} {ld:>9.1f} {e:>14.1f} {e/k:>8.4f}")

H = -(1/L)*log2(1/L) - (1-1/L)*log2(1-1/L)
print(f"\nentropy of the band  H(log2/log3) = {H:.4f}   deficit = {1-H:.4f}")
print("so the heuristic margin is ~2^(-0.05 k), EXPONENTIAL.")
print("\nBaker's loss on D is only quasi-polynomial: D > 2^k * exp(-C log^2 k).")
for k in (10**3, 10**5, 10**7):
    print(f"  k={k:>9}:  Baker loss exp2 ~ {1.44*25*log(k)**2:>12.0f}   "
          f"entropy budget 0.05k = {0.05*k:>12.0f}   "
          f"{'BUDGET WINS' if 0.05*k > 1.44*25*log(k)**2 else 'loss wins'}")
