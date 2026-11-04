/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.SliceTelescopeStep

/-!
# SEC6S lap 1 (third part): the unrolled multi-scale telescope

Iterating the one-step telescope `levelOsc_succ_le_telescope` from scale `a` down to `m`
(`SEC6S-PLAN.md` §2(b), Tao's unrolled (6.1)): for `m < a`,

    levelOsc j a m ≤ levelOsc j a (a−1)
                     + Σ_{k=m+1}^{a−1} Σ_{j' < j} C(j − j' − 1, a − k − 1) · levelOsc j' k (k−1).

The weight `C(j − j' − 1, s − 1)` counts the chains `j > ℓ₁ > ⋯ > ℓ_{s−1} > j'` of slice lengths
produced by `s = a − k` applications of the one-step rule (each step replaces a length `ℓ` by some
`t − 1 < ℓ`).  Proof: induction on `a` from `a = m + 1` (where the sum is empty and the bound is an
equality); the step applies `levelOsc_succ_le_telescope j a m`, then the hypothesis at each
`(t − 1, a, m)`, and sums: the `levelOsc (t−1) a (a−1)` terms are the new `k = a` layer (weight
`C(j − j' − 1, 0) = 1`), and the inner layers collapse by the hockey stick
`Σ_{u ≤ n} C(u, r) = C(n + 1, r + 1)` applied to `Σ_{t = j'+2}^{j} C(t − 2 − j', a − k − 1) = C(j − j' − 1, a − k)`.
Exact check: `experiments/conjugacy/unroll.py` (286 triples, `j ≤ 11`, 0 violations; dropping the
first term fails 112/286; the weight `C(j − j' − 1, a − k)` fails 100/286; the bound is attained).
-/

namespace CollatzMoonshot.Conjugacy

open Finset CollatzMoonshot.FrontB

/-- The hockey-stick collapse of one layer: summing the chain weights `C(i − j' − 1, r)` over the
intermediate length `i < j` raises the weight to `C(j − j' − 1, r + 1)`. -/
theorem sum_range_sum_range_choose (r : ℕ) (y : ℕ → ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range j, ∑ j' ∈ Finset.range i, ((i - j' - 1).choose r : ℝ) * y j' =
      ∑ j' ∈ Finset.range j, ((j - j' - 1).choose (r + 1) : ℝ) * y j' := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun j' => ((j + 1 - j' - 1).choose (r + 1) : ℝ) * y j') j]
    have h0 : (j + 1 - j - 1).choose (r + 1) = 0 := by simp
    rw [h0, Nat.cast_zero, zero_mul, add_zero, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j' hj' => ?_
    have hj : j' < j := Finset.mem_range.mp hj'
    have h1 : j + 1 - j' - 1 = (j - j' - 1) + 1 := by omega
    rw [h1, Nat.choose_succ_succ, Nat.cast_add]
    ring

/-- **Frozen.**  The unrolled multi-scale telescope for the slice oscillations: for `m < a`,
`osc_{m,a}` of the slice `(j, a)` is at most its top-scale oscillation plus the binomially weighted
top-scale oscillations of the shorter slices at every intermediate scale. -/
theorem levelOsc_le_unrolled (j a m : ℕ) (hm : m < a) :
    levelOsc j a m ≤ levelOsc j a (a - 1) +
      ∑ k ∈ Finset.Ico (m + 1) a, ∑ j' ∈ Finset.range j,
        ((j - j' - 1).choose (a - k - 1) : ℝ) * levelOsc j' k (k - 1) := by
  induction a, hm using Nat.le_induction generalizing j with
  | base => simp
  | succ a ha ih =>
    have hstep := levelOsc_succ_le_telescope j a m (by omega)
    have hre : ∑ t ∈ Finset.Icc 1 j, levelOsc (t - 1) a m =
        ∑ i ∈ Finset.range j, levelOsc i a m := by
      have hI : Finset.Icc 1 j = Finset.Ico 1 (j + 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hI, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by simp) fun i _ => ?_
      congr 1; omega
    rw [hre] at hstep
    have hih : ∑ i ∈ Finset.range j, levelOsc i a m ≤
        ∑ i ∈ Finset.range j, (levelOsc i a (a - 1) +
          ∑ k ∈ Finset.Ico (m + 1) a, ∑ j' ∈ Finset.range i,
            ((i - j' - 1).choose (a - k - 1) : ℝ) * levelOsc j' k (k - 1)) :=
      Finset.sum_le_sum fun i _ => ih i
    rw [Finset.sum_add_distrib, Finset.sum_comm] at hih
    have hcol : ∀ k ∈ Finset.Ico (m + 1) a,
        ∑ i ∈ Finset.range j, ∑ j' ∈ Finset.range i,
            ((i - j' - 1).choose (a - k - 1) : ℝ) * levelOsc j' k (k - 1) =
          ∑ j' ∈ Finset.range j,
            ((j - j' - 1).choose (a + 1 - k - 1) : ℝ) * levelOsc j' k (k - 1) := by
      intro k hk
      have hk' : k < a := (Finset.mem_Ico.mp hk).2
      rw [sum_range_sum_range_choose]
      refine Finset.sum_congr rfl fun j' _ => ?_
      congr 3; omega
    rw [Finset.sum_congr rfl hcol] at hih
    rw [Finset.sum_Ico_succ_top (by omega : m + 1 ≤ a)]
    have htop : ∑ j' ∈ Finset.range j,
        ((j - j' - 1).choose (a + 1 - a - 1) : ℝ) * levelOsc j' a (a - 1) =
          ∑ j' ∈ Finset.range j, levelOsc j' a (a - 1) := by
      refine Finset.sum_congr rfl fun j' _ => ?_
      simp
    rw [htop, Nat.add_sub_cancel]
    linarith

end CollatzMoonshot.Conjugacy
