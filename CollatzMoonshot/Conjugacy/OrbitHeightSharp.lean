/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitHeightLaw

/-!
# The height line, all the way to `C*`

`heightLawUpTo_four` stops at `t = 4 size n` for reasons of bookkeeping: the letter-`1` tolerance
`1 / 100`, the number of scales `numScales = 4000`, and the horizon `21 / 5` in `GoodOdd` are fixed
numbers.  Letting them depend on `τ` should carry the line through every `τ < 1 / β`, and
`not_heightLawUpTo_of_gt` ends it there.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- **The height line through every `τ < 1 / β`.**  Believed, 90%. -/
theorem heightLawBelowThreshold : HeightLawBelowThreshold := by
  sorry

/-- **`C* = 1 / β` is the sharp end of the height line.** -/
theorem heightLawUpTo_iff {τ : ℝ} (hτ : τ * heightSlope ≠ 1) :
    HeightLawUpTo τ ↔ τ * heightSlope < 1 :=
  ⟨fun h => lt_of_le_of_ne (not_lt.mp fun hgt => not_heightLawUpTo_of_gt hgt h) hτ,
    fun h => heightLawBelowThreshold τ h⟩

/-- **First passage below `n^θ`, for every `0 < θ < 1`.**  From `heightLawBelowThreshold`.
Confidence 90%. -/
theorem firstPassage_sharp {θ ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    LogDens0 fun n : ℕ => ¬ (
      (∀ t : ℕ, (t : ℝ) ≤ ((1 - θ) / heightSlope - ε) * Nat.size n →
        (n : ℝ) ^ θ < (tstep^[t] n : ℝ)) ∧
      ∃ t : ℕ, (t : ℝ) ≤ ((1 - θ) / heightSlope + ε) * Nat.size n ∧
        (tstep^[t] n : ℝ) ≤ (n : ℝ) ^ θ) := by
  have hβ := heightSlope_pos
  have hβ5 := heightSlope_le
  set c : ℝ := (1 - θ) / heightSlope with hc
  have hcβ : heightSlope * c = 1 - θ := by rw [hc]; field_simp
  have hc0 : 0 < c := div_pos (by linarith) hβ
  set η : ℝ := min ε (θ / (2 * heightSlope)) with hηdef
  have hη : 0 < η := lt_min hε (by positivity)
  have hηε : η ≤ ε := min_le_left _ _
  have hηθ : η * heightSlope ≤ θ / 2 := by
    have h := (le_div_iff₀ (by positivity)).mp (min_le_right ε (θ / (2 * heightSlope)))
    linarith
  set τ : ℝ := c + η with hτdef
  have hτ : τ * heightSlope < 1 := by
    have : τ * heightSlope = heightSlope * c + η * heightSlope := by rw [hτdef]; ring
    rw [this, hcβ]
    linarith
  set ε₀ : ℝ := heightSlope * η / 2 with hε₀def
  have hε₀ : 0 < ε₀ := by positivity
  set K : ℕ := ⌈1 / ε₀⌉₊ with hK
  refine ((heightLawBelowThreshold τ hτ ε₀ hε₀).or
    (logDens0_of_bdd (B := 2 ^ (K + 1)) fun n h => h)).mono fun n hbad => ?_
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨hgood, hn⟩ := hcon
  have hn1 : 1 ≤ n := by
    have : 0 < 2 ^ (K + 1) := by positivity
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsize : K + 1 < Nat.size n := Nat.lt_size.mpr hn.le
  have hsn : (0 : ℝ) ≤ Nat.size n := Nat.cast_nonneg _
  have hlarge : 1 < ε₀ * Nat.size n := by
    have h1 : 1 / ε₀ ≤ K := Nat.le_ceil _
    rw [div_le_iff₀ hε₀] at h1
    have h2 : ((K : ℕ) : ℝ) + 1 ≤ Nat.size n := by exact_mod_cast (by omega : K + 1 ≤ Nat.size n)
    nlinarith
  have hline : ∀ t : ℕ, (t : ℝ) ≤ τ * Nat.size n →
      |Real.logb 2 (tstep^[t] n) - (Real.logb 2 n - heightSlope * t)| ≤ ε₀ * Nat.size n := by
    intro t ht
    by_contra hlt
    exact hgood ⟨t, ht, not_le.mp hlt⟩
  have hlog := logb_lt_size hn1
  have hlog2 := size_le_logb_add_one hn1
  have h1θ : 0 < 1 - θ := by linarith
  apply hbad
  constructor
  · intro t ht
    have ht4 : (t : ℝ) ≤ τ * Nat.size n := by
      refine le_trans ht (mul_le_mul_of_nonneg_right ?_ hsn)
      linarith
    have hdev := abs_le.mp (hline t ht4)
    have hy1 : (0 : ℝ) < tstep^[t] n := by exact_mod_cast one_le_tstep_iterate hn1 t
    rw [← Real.logb_lt_logb_iff (b := 2) (by norm_num) (Real.rpow_pos_of_pos hnR θ) hy1,
      Real.logb_rpow_eq_mul_logb_of_pos hnR]
    have h1 : heightSlope * t ≤ heightSlope * ((c - ε) * Nat.size n) :=
      mul_le_mul_of_nonneg_left ht hβ.le
    have h2 : (1 - θ) * ((Nat.size n : ℝ) - 1) ≤ (1 - θ) * Real.logb 2 n :=
      mul_le_mul_of_nonneg_left (by linarith) h1θ.le
    have h3 : heightSlope * ((c - ε) * Nat.size n) =
        (1 - θ) * Nat.size n - heightSlope * ε * Nat.size n := by
      rw [← hcβ]
      ring
    have h4 : 2 * ε₀ * Nat.size n ≤ heightSlope * ε * Nat.size n := by
      refine mul_le_mul_of_nonneg_right ?_ hsn
      rw [hε₀def]
      nlinarith
    nlinarith
  · have hτ0 : 0 ≤ τ * Nat.size n := by positivity
    refine ⟨⌊τ * Nat.size n⌋₊, ?_, ?_⟩
    · refine le_trans (Nat.floor_le hτ0) (mul_le_mul_of_nonneg_right ?_ hsn)
      linarith
    · have hdev := abs_le.mp (hline _ (Nat.floor_le hτ0))
      have hy1 : (0 : ℝ) < tstep^[⌊τ * Nat.size n⌋₊] n := by
        exact_mod_cast one_le_tstep_iterate hn1 _
      rw [← Real.logb_le_logb (b := 2) (by norm_num) hy1 (Real.rpow_pos_of_pos hnR θ),
        Real.logb_rpow_eq_mul_logb_of_pos hnR]
      have hfl := Nat.lt_floor_add_one (τ * Nat.size n)
      have h1 := mul_lt_mul_of_pos_left hfl hβ
      have h2 : (1 - θ) * Real.logb 2 n ≤ (1 - θ) * Nat.size n :=
        mul_le_mul_of_nonneg_left hlog.le h1θ.le
      have h3 : heightSlope * (τ * Nat.size n) =
          (1 - θ) * Nat.size n + 2 * (ε₀ * Nat.size n) := by
        rw [hε₀def, hτdef, ← hcβ]
        ring
      nlinarith

end CollatzMoonshot.Conjugacy
