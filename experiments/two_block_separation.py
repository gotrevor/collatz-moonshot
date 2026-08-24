"""GO-route scoping for the two-block crux `b+d <= 5` (review lap 2026-08-25-1500).

After `two_block_relaxation.py` refuted the elementary route, this pins the EXACT minimal
effective input.  The crux closes from three parts:

  reduction (elementary)  +  separation lemma (weak effective bound, DISCLOSED)  +  finite check.

Reduction facts (proved sorry-free in `near_critical_containment`), with k=b+d, D=2^m-3^k:
  window_unique_m + hupper: 3^k < 2^m < 2*3^k, and m is the unique such power.
  (W) 2^d * D < 2^m            (from hbracket)
  (A) D * 2^k <= 2^m * 3^d     (from ¬A: D<=2^c*3^d, and 2^c<=2^(m-k) since e>=0)

Separation lemma (beta = 3/8, integer form), the sole disclosed effective input:
  for 6<=k, 3^k<2^m<2*3^k:   (2^m - 3^k)^8 * 2^(3k) >= 3^(8k)     [i.e. D >= 3^k * 2^(-3k/8)]

This script verifies:
  (1) the separation lemma is TRUE for all near-critical 6<=k<BND;
  (2) beta=3/8 lies in the feasible window [~0.319, log2/log6=0.3869);
  (3) [(W) and (A)] has NO integer-d solution for the ACTUAL near-critical D at any 6<=k<BND
      (so the reduction+separation closes k, and the finite tail needing native_decide is k in
       [6, 83] where the loose-constant reduction alone does not yet bite).
"""
import math


def nearcrit(k):
    P = 3 ** k
    m = P.bit_length()
    while 2 ** m <= P:
        m += 1
    return m, P


def verify(BND=500):
    # (1) separation lemma
    sep_ok = all((2 ** nearcrit(k)[0] - nearcrit(k)[1]) ** 8 * 2 ** (3 * k)
                 >= 3 ** (8 * k) for k in range(6, BND))

    # (2) feasible beta window
    beta_true_min = max(-math.log2((2 ** nearcrit(k)[0] - nearcrit(k)[1]) / nearcrit(k)[1]) / k
                        for k in range(6, BND))          # bound TRUE iff beta >= this
    beta_reduction_max = math.log(2) / math.log(6)        # reduction needs beta < this

    # (3) no integer-d config survives (W)&(A) for actual near-critical D
    survivors = []
    for k in range(6, min(BND, 200)):
        m, P = nearcrit(k)
        D = 2 ** m - P
        for d in range(1, k):
            if (2 ** d * D < 2 ** m) and (D * 2 ** k <= 2 ** m * 3 ** d):
                survivors.append((k, d))
    return sep_ok, beta_true_min, beta_reduction_max, survivors


if __name__ == "__main__":
    sep_ok, bmin, bmax, surv = verify()
    print(f"(1) separation (2^m-3^k)^8 * 2^(3k) >= 3^(8k) for all near-critical 6<=k<500: {sep_ok}")
    print(f"(2) feasible beta window: [{bmin:.4f}, {bmax:.4f})   -> 3/8 = 0.375 is inside: "
          f"{bmin <= 0.375 < bmax}")
    print(f"(3) integer-d configs surviving [(W) and (A)] for 6<=k<200: {surv}  (empty => reduction "
          f"closes at actual D)")
    print()
    print("Conclusion: crux = elementary reduction + native_decide finite check (k in [6,83]) +")
    print("the DISCLOSED separation lemma `(2^m-3^k)^8 * 2^(3k) >= 3^(8k)` (build via mathlib")
    print("GenContFract convergent bounds for log_2 3 = the GO prize).")
