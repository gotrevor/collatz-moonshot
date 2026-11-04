/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.SliceTelescope

/-!
# SEC6S lap 1 (second half): the one-step telescope for slice oscillations

Tao's (6.1) for the sliced laws (`SEC6S-PLAN.md` §2(b)): for `m ≤ a`,

    levelOsc j (a+1) m ≤ levelOsc j (a+1) a + Σ_{t=1}^{j} levelOsc (t − 1) a m.

Proof: for `y < 3^{a+1}` put `ȳ = y % 3^a`; then `y % 3^m = ȳ % 3^m` and
`3^m/3^{a+1} = (1/3)·(3^m/3^a)`, so the pointwise triangle inequality gives
`|mass y − 3^m/3^{a+1}·class_m (y % 3^m)| ≤ |mass y − 3^a/3^{a+1}·class_a ȳ| + (1/3)|class_a ȳ − 3^m/3^a·class_m (ȳ % 3^m)|`
with `mass = levelMass j (a+1)`, `class_k = levelClass j (a+1) k`.  Summing over `y < 3^{a+1}`:
the first sum is `levelOsc j (a+1) a`; in the second each `ȳ < 3^a` has exactly three lifts
`ȳ + i·3^a`, `i < 3`, which cancels the `1/3`.  Now `class_a ȳ = Σ_t levelMass (t−1) a ȳ`
(`levelClass_eq_sum_levelMass` at `a' = a`, weights `C(j−t, 0) = 1`) and
`class_m c = Σ_t levelClass (t−1) a m c` (the same Pascal induction, `levelClass_succ_pascal`,
on the class counts), so the remaining sum is `Σ_ȳ |Σ_t (levelMass (t−1) a ȳ − 3^m/3^a·levelClass (t−1) a m (ȳ % 3^m))|`,
which is `≤ Σ_t levelOsc (t−1) a m` by `|Σ| ≤ Σ|·|` and swapping the sums.  Exact check:
`experiments/conjugacy/telescope.py` (364 triples, `j ≤ 12`, 0 violations; dropping the first
term fails 332/364; the bound is attained).
-/

namespace CollatzMoonshot.Conjugacy

open Finset CollatzMoonshot.FrontB

/-- Consistency of the class counts: for `m ≤ a`, the class count of the slice `(j, a + 1)` mod
`3^m` is the sum of the class counts of the shorter slices `(t − 1, a)`, `1 ≤ t ≤ j`. -/
theorem levelClass_succ_eq_sum_levelClass (j a m c : ℕ) (hm : m ≤ a) :
    levelClass j (a + 1) m c = ∑ t ∈ Finset.Icc 1 j, levelClass (t - 1) a m c := by
  induction j with
  | zero => simp [levelClass_zero_succ]
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega), levelClass_succ_pascal j a m c hm, ih,
      Nat.add_sub_cancel]

/-- Each residue `z < N` has exactly `k` lifts `z + i·N`, `i < k`, in `range (k·N)`. -/
theorem sum_range_mul_mod (N : ℕ) (g : ℕ → ℝ) : ∀ k : ℕ,
    ∑ y ∈ Finset.range (k * N), g (y % N) = (k : ℝ) * ∑ z ∈ Finset.range N, g z := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have h : ∑ y ∈ Finset.range N, g ((k * N + y) % N) = ∑ z ∈ Finset.range N, g z := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Finset.mem_range.mp hy)]
    rw [h]
    push_cast
    ring

/-- **Frozen.**  One-step telescope for the slice oscillations (Tao's (6.1) for slices): for
`m ≤ a`, `osc_{m,a+1}` of the slice `(j, a+1)` is at most its last-scale oscillation `osc_{a,a+1}`
plus the sum of the `osc_{m,a}` of the shorter slices `(t − 1, a)`, `1 ≤ t ≤ j`. -/
theorem levelOsc_succ_le_telescope (j a m : ℕ) (hm : m ≤ a) :
    levelOsc j (a + 1) m ≤
      levelOsc j (a + 1) a + ∑ t ∈ Finset.Icc 1 j, levelOsc (t - 1) a m := by
  have hmod : ∀ y, y % 3 ^ a % 3 ^ m = y % 3 ^ m := fun y =>
    Nat.mod_mod_of_dvd y (pow_dvd_pow 3 hm)
  set g : ℕ → ℝ := fun z => |(levelClass j (a + 1) a z : ℝ) -
    (3 : ℝ) ^ m / 3 ^ a * levelClass j (a + 1) m (z % 3 ^ m)| with hg
  have hpt : ∀ y, |(levelMass j (a + 1) y : ℝ) -
      (3 : ℝ) ^ m / 3 ^ (a + 1) * levelClass j (a + 1) m (y % 3 ^ m)| ≤
      |(levelMass j (a + 1) y : ℝ) -
        (3 : ℝ) ^ a / 3 ^ (a + 1) * levelClass j (a + 1) a (y % 3 ^ a)| +
      (1 / 3) * g (y % 3 ^ a) := by
    intro y
    have e : (levelMass j (a + 1) y : ℝ) -
        (3 : ℝ) ^ m / 3 ^ (a + 1) * levelClass j (a + 1) m (y % 3 ^ m) =
        ((levelMass j (a + 1) y : ℝ) -
          (3 : ℝ) ^ a / 3 ^ (a + 1) * levelClass j (a + 1) a (y % 3 ^ a)) +
        (1 / 3) * ((levelClass j (a + 1) a (y % 3 ^ a) : ℝ) -
          (3 : ℝ) ^ m / 3 ^ a * levelClass j (a + 1) m (y % 3 ^ a % 3 ^ m)) := by
      rw [hmod y]
      field_simp
      ring
    rw [e]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)]
  have hsum1 : levelOsc j (a + 1) m ≤
      levelOsc j (a + 1) a + (1 / 3) * ∑ y ∈ Finset.range (3 ^ (a + 1)), g (y % 3 ^ a) := by
    unfold levelOsc
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun y _ => hpt y
  have hsum2 : ∑ y ∈ Finset.range (3 ^ (a + 1)), g (y % 3 ^ a) =
      3 * ∑ z ∈ Finset.range (3 ^ a), g z := by
    rw [pow_succ, mul_comm, sum_range_mul_mod]
    norm_num
  have hg_le : ∀ z, g z ≤ ∑ t ∈ Finset.Icc 1 j, |(levelMass (t - 1) a z : ℝ) -
      (3 : ℝ) ^ m / 3 ^ a * levelClass (t - 1) a m (z % 3 ^ m)| := by
    intro z
    simp only [hg]
    rw [levelClass_succ_eq_sum_levelClass j a a z le_rfl,
      levelClass_succ_eq_sum_levelClass j a m _ hm]
    simp only [levelClass_self]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  calc levelOsc j (a + 1) m
      ≤ levelOsc j (a + 1) a + (1 / 3) * ∑ y ∈ Finset.range (3 ^ (a + 1)), g (y % 3 ^ a) :=
        hsum1
    _ = levelOsc j (a + 1) a + ∑ z ∈ Finset.range (3 ^ a), g z := by rw [hsum2]; ring
    _ ≤ levelOsc j (a + 1) a + ∑ z ∈ Finset.range (3 ^ a), ∑ t ∈ Finset.Icc 1 j,
          |(levelMass (t - 1) a z : ℝ) -
            (3 : ℝ) ^ m / 3 ^ a * levelClass (t - 1) a m (z % 3 ^ m)| := by
        gcongr with z
        exact hg_le z
    _ = levelOsc j (a + 1) a + ∑ t ∈ Finset.Icc 1 j, levelOsc (t - 1) a m := by
        rw [Finset.sum_comm]
        rfl

end CollatzMoonshot.Conjugacy
