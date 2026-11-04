/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitHeightSharpReadOff

/-!
# The height line to `C*`: from the letter `1` to the height

`GoodOddUpTo δ τ m` keeps the orbit of an odd `m` within `2 δ size m` of the line, up to the
correction `heightCorr`, through `τ size m` (`height_lower_of_goodOddUpTo`).  With `γ = 1 − τ β`
and `4 δ ≤ γ`, every height before `τ size m` is at least `2^(γ size m / 2 − 1)`, so the correction
is at most `t / 2^K` once `γ size m ≥ 2 (K + 1)` (`heightCorr_le_of_goodOddUpTo`).  For the even
starts `2^a m`, the first `a` letters are halvings, and the rest is the orbit of `m`
(`abs_height_sub_line_le_two_pow_mul_upTo`).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-- `log₂ 3 ≤ 2`. -/
theorem logb_three_le_two : Real.logb 2 3 ≤ 2 := by linarith [logb_three_lt]

/-- The deviation from the line, against `GoodOddUpTo`: within `2 δ size m` of `heightCorr`. -/
theorem abs_height_sub_line_sub_corr_le {δ τ : ℝ} {m T : ℕ} (hm : 1 ≤ m)
    (hg : GoodOddUpTo δ τ m) (hT : (T : ℝ) ≤ τ * Nat.size m) :
    |Real.logb 2 (tstep^[T] m) - (Real.logb 2 m - heightSlope * T) - heightCorr m T| ≤
      2 * (δ * Nat.size m) := by
  have hdev := hg T hT
  rw [wdev_true_eq] at hdev
  rw [height_sub_line_eq hm T, add_sub_cancel_right, abs_mul,
    abs_of_nonneg (by linarith [one_le_logb_three] : (0 : ℝ) ≤ Real.logb 2 3)]
  calc |(oddCount m T : ℝ) - T / 2| * Real.logb 2 3 ≤ (δ * Nat.size m) * 2 :=
        mul_le_mul hdev logb_three_le_two (by linarith [one_le_logb_three])
          (le_trans (abs_nonneg _) hdev)
    _ = 2 * (δ * Nat.size m) := by ring

/-- On the prefixes `GoodOddUpTo` controls, the height is at least `log₂ m − βT − 2 δ size m`. -/
theorem height_lower_of_goodOddUpTo {δ τ : ℝ} {m T : ℕ} (hm : 1 ≤ m)
    (hg : GoodOddUpTo δ τ m) (hT : (T : ℝ) ≤ τ * Nat.size m) :
    Real.logb 2 m - heightSlope * T - 2 * (δ * Nat.size m) ≤ Real.logb 2 (tstep^[T] m) := by
  have h := (abs_le.mp (abs_height_sub_line_sub_corr_le hm hg hT)).1
  have hc := heightCorr_nonneg hm T
  linarith

/-- **The correction is small.**  With `γ = 1 − τ β`, `4 δ ≤ γ` and `γ size m ≥ 2 (K + 1)`, every
odd height before `T ≤ τ size m` is at least `2^K`, so `heightCorr m T ≤ T / 2^K`. -/
theorem heightCorr_le_of_goodOddUpTo {δ τ : ℝ} {m T K : ℕ} (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (hδγ : 4 * δ ≤ 1 - τ * heightSlope) (hm : 1 ≤ m)
    (hs : 2 * ((K : ℝ) + 1) ≤ (1 - τ * heightSlope) * Nat.size m) (hg : GoodOddUpTo δ τ m)
    (hT : (T : ℝ) ≤ τ * Nat.size m) :
    heightCorr m T ≤ T / 2 ^ K := by
  have hβ := heightSlope_pos
  have hsn : (0 : ℝ) ≤ Nat.size m := Nat.cast_nonneg _
  have hle : ∀ i < T, tstep^[i] m % 2 = 1 → 2 ^ K ≤ tstep^[i] m := by
    intro i hi _
    have hiR : (i : ℝ) ≤ τ * Nat.size m := by
      have : (i : ℝ) ≤ T := by exact_mod_cast hi.le
      linarith
    have hlow := height_lower_of_goodOddUpTo hm hg hiR
    have hlog := size_le_logb_add_one hm
    have h1 : heightSlope * i ≤ heightSlope * (τ * Nat.size m) :=
      mul_le_mul_of_nonneg_left hiR hβ.le
    have h2 : 4 * δ * Nat.size m ≤ (1 - τ * heightSlope) * Nat.size m :=
      mul_le_mul_of_nonneg_right hδγ hsn
    have hkey : (K : ℝ) ≤ Real.logb 2 (tstep^[i] m) := by
      have : heightSlope * (τ * Nat.size m) = τ * heightSlope * Nat.size m := by ring
      linarith
    have hpos : (0 : ℝ) < tstep^[i] m := by exact_mod_cast one_le_tstep_iterate hm i
    have hp2 : ((2 : ℝ) ^ K) ≤ tstep^[i] m := by
      rw [← Real.logb_le_logb (b := 2) (by norm_num) (by positivity) hpos, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num), mul_one]
      exact hkey
    exact_mod_cast hp2
  have hc := heightCorr_le_of_ge Nat.one_le_two_pow hle
  push_cast at hc
  exact hc

/-- **The odd core.**  A good odd `m` stays within `2 δ size m + T / 2^K` of the line. -/
theorem abs_height_sub_line_le_of_goodOddUpTo {δ τ : ℝ} {m T K : ℕ} (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (hδγ : 4 * δ ≤ 1 - τ * heightSlope) (hm : 1 ≤ m)
    (hs : 2 * ((K : ℝ) + 1) ≤ (1 - τ * heightSlope) * Nat.size m) (hg : GoodOddUpTo δ τ m)
    (hT : (T : ℝ) ≤ τ * Nat.size m) :
    |Real.logb 2 (tstep^[T] m) - (Real.logb 2 m - heightSlope * T)| ≤
      2 * (δ * Nat.size m) + T / 2 ^ K := by
  have h := abs_height_sub_line_sub_corr_le hm hg hT
  have hc := heightCorr_le_of_goodOddUpTo hτ hδ hδγ hm hs hg hT
  have hc0 := heightCorr_nonneg hm T
  have := abs_add_le (Real.logb 2 (tstep^[T] m) - (Real.logb 2 m - heightSlope * T) -
    heightCorr m T) (heightCorr m T)
  rw [sub_add_cancel, abs_of_nonneg hc0] at this
  linarith

/-- **The even reduction.**  A start `2^a m` with `m` good through `τ size m`, at a time
`t ≤ τ₁ size (2^a m)` with `τ₁ (size m + a) − a ≤ τ size m`, stays within `a` more of the line. -/
theorem abs_height_sub_line_le_two_pow_mul_upTo {δ τ τ₁ : ℝ} {a m t K : ℕ} (hτ : 0 ≤ τ)
    (hδ : 0 ≤ δ) (hδγ : 4 * δ ≤ 1 - τ * heightSlope) (hm : 1 ≤ m)
    (hs : 2 * ((K : ℝ) + 1) ≤ (1 - τ * heightSlope) * Nat.size m) (hg : GoodOddUpTo δ τ m)
    (hτa : τ₁ * (Nat.size m + a) - a ≤ τ * Nat.size m)
    (ht : (t : ℝ) ≤ τ₁ * (Nat.size m + a)) :
    |Real.logb 2 (tstep^[t] (2 ^ a * m)) - (Real.logb 2 ((2 ^ a * m : ℕ) : ℝ) - heightSlope * t)| ≤
      2 * (δ * Nat.size m) + τ * Nat.size m / 2 ^ K + a := by
  have hβ0 := heightSlope_pos
  have hβ1 : heightSlope ≤ 1 := by linarith [heightSlope_le]
  have hsn : (0 : ℝ) ≤ Nat.size m := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hδs : 0 ≤ 2 * (δ * Nat.size m) := by positivity
  have hτs : 0 ≤ τ * Nat.size m / 2 ^ K := by positivity
  rcases le_or_gt t a with hta | hta
  · -- only halvings so far
    obtain ⟨b, rfl⟩ : ∃ b, a = t + b := ⟨a - t, by omega⟩
    have hM : 1 ≤ 2 ^ b * m := Nat.mul_pos (by positivity) hm
    have hnm : 2 ^ (t + b) * m = 2 ^ t * (2 ^ b * m) := by rw [pow_add, mul_assoc]
    rw [hnm, tstep_iterate_two_pow_mul, logb_two_pow_mul t hM]
    have hexp : Real.logb 2 ((2 ^ b * m : ℕ) : ℝ) -
        (t + Real.logb 2 ((2 ^ b * m : ℕ) : ℝ) - heightSlope * t) = -((1 - heightSlope) * t) := by
      ring
    rw [hexp, abs_neg, abs_of_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _))]
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    have h1 : (1 - heightSlope) * t ≤ t := by nlinarith
    push_cast
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    linarith
  · -- past the halvings, the orbit of `m`
    obtain ⟨T, rfl⟩ : ∃ T, t = T + a := ⟨t - a, by omega⟩
    rw [Function.iterate_add_apply, tstep_iterate_two_pow_mul, logb_two_pow_mul a hm]
    have hT : (T : ℝ) ≤ τ * Nat.size m := by
      push_cast at ht
      linarith
    have hcore := abs_height_sub_line_le_of_goodOddUpTo hτ hδ hδγ hm hs hg hT
    have hTK : (T : ℝ) / 2 ^ K ≤ τ * Nat.size m / 2 ^ K :=
      div_le_div_of_nonneg_right hT (by positivity)
    have hexp : Real.logb 2 (tstep^[T] m) - (a + Real.logb 2 m - heightSlope * ((T + a : ℕ) : ℝ)) =
        (Real.logb 2 (tstep^[T] m) - (Real.logb 2 m - heightSlope * T)) -
          ((1 - heightSlope) * a) := by
      push_cast
      ring
    rw [hexp]
    refine le_trans (abs_sub _ _) ?_
    rw [abs_of_nonneg (mul_nonneg (by linarith) ha0)]
    have h1 : (1 - heightSlope) * a ≤ a := by nlinarith
    linarith

/-- The height law gets weaker as the horizon shrinks. -/
theorem HeightLawUpTo.mono {τ τ' : ℝ} (h : HeightLawUpTo τ') (hτ : τ ≤ τ') : HeightLawUpTo τ :=
  fun ε hε => (h ε hε).mono fun n ⟨t, ht, hdev⟩ =>
    ⟨t, le_trans ht (mul_le_mul_of_nonneg_right hτ (Nat.cast_nonneg _)), hdev⟩

end CollatzMoonshot.Conjugacy
