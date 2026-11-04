/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitHeightSharpLine

/-!
# The height line, all the way to `C*`

`heightLawUpTo_four` stops at `t = 4 size n` for reasons of bookkeeping: the letter-`1` tolerance
`1 / 100`, the number of scales `numScales = 4000`, and the horizon `21 / 5` in `GoodOdd` are fixed
numbers.  Letting them depend on `τ` carries the line through every `τ < 1 / β`
(`heightLawBelowThreshold`), and `not_heightLawUpTo_of_gt` ends it there.  For the word `[true]` the
letter-`1` tolerance is the word's own `δ`; the number of scales `J` has `α^(−J) ≤ (1 − τβ) / 4`
(`goodOddUpTo_of_stages`); and the horizon is `τ₁ + (1 − τ₁ β) / (2 β)`, which leaves room for the
even reduction (`heightLawUpTo_of_one_le`).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- **A good even start is not bad.**  `2^a m` with `m` good through `τ size m` stays within
`ε size (2^a m)` of the line through `τ₁ size (2^a m)`, once the halvings `a` are few, `size m` is
large, and `2^K` beats the length of the orbit. -/
theorem not_badHeight_two_pow_mul {τ₁ τ δ ε : ℝ} {a m K : ℕ} (hτ0 : 0 ≤ τ) (hδ : 0 ≤ δ)
    (hε : 0 < ε) (hδγ : 4 * δ ≤ 1 - τ * heightSlope) (hδε : δ ≤ ε / 8)
    (hK : 4 * τ ≤ ε * 2 ^ K) (hm : 1 ≤ m) (hs1 : 1 ≤ Nat.size m)
    (hsγ : 2 * ((K : ℝ) + 1) ≤ (1 - τ * heightSlope) * Nat.size m)
    (hτa : τ₁ * (Nat.size m + a) - a ≤ τ * Nat.size m) (haε : (a : ℝ) ≤ ε / 4 * Nat.size m)
    (hg : GoodOddUpTo δ τ m) : ¬ BadHeight τ₁ ε (2 ^ a * m) := by
  rintro ⟨t, ht, hdev⟩
  have hm0 : m ≠ 0 := by omega
  rw [size_two_pow_mul hm0] at ht hdev
  push_cast at ht
  have hle := abs_height_sub_line_le_two_pow_mul_upTo hτ0 hδ hδγ hm hsγ hg hτa ht
  push_cast at hdev hle
  have hsn : (1 : ℝ) ≤ Nat.size m := by exact_mod_cast hs1
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hδs : δ * Nat.size m ≤ ε / 8 * Nat.size m :=
    mul_le_mul_of_nonneg_right hδε (by linarith)
  have hτs : τ * Nat.size m / 2 ^ K ≤ ε / 4 * Nat.size m := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hK (by linarith : (0 : ℝ) ≤ Nat.size m)
    linarith
  have hεa : 0 ≤ ε * a := mul_nonneg hε.le ha0
  have hεs : 0 < ε * Nat.size m := mul_pos hε (by linarith)
  linarith

/-- **The height line through `τ₁ size n`, for `1 ≤ τ₁ < 1 / β`.**  From `goodOddUpTo_whp` at the
horizon `τ = τ₁ + μ`, `μ = (1 − τ₁ β) / (2 β)`, which leaves room for the even reduction:
`t − a ≤ τ₁ (size m + a) − a ≤ τ size m` once `τ₁ a ≤ μ size m`. -/
theorem heightLawUpTo_of_one_le {τ₁ : ℝ} (h1 : 1 ≤ τ₁) (hτ₁ : τ₁ * heightSlope < 1) :
    HeightLawUpTo τ₁ := by
  intro ε hε
  have hβ := heightSlope_pos
  set μ : ℝ := (1 - τ₁ * heightSlope) / (2 * heightSlope) with hμ
  have hμ0 : 0 < μ := div_pos (by linarith) (by positivity)
  set τ : ℝ := τ₁ + μ with hτdef
  have hτβ : τ * heightSlope = (τ₁ * heightSlope + 1) / 2 := by
    rw [hτdef, hμ]
    field_simp
    ring
  have hγ : 0 < 1 - τ * heightSlope := by linarith
  have hτ0 : 0 < τ := by linarith
  set δ : ℝ := min ((1 - τ * heightSlope) / 4) (ε / 8) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδγ : 4 * δ ≤ 1 - τ * heightSlope := by
    linarith [min_le_left ((1 - τ * heightSlope) / 4) (ε / 8)]
  set K : ℕ := ⌈4 * τ / ε⌉₊ with hKdef
  have hK : 4 * τ ≤ ε * 2 ^ K := by
    have h2 : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast Nat.lt_two_pow_self.le
    have h3 := le_trans (Nat.le_ceil (4 * τ / ε)) h2
    rw [div_le_iff₀ hε] at h3
    linarith
  set ε' : ℝ := min 1 (min (μ / τ₁) (ε / 4)) with hε'def
  have hε' : 0 < ε' := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hε'1 : ε' ≤ 1 := min_le_left _ _
  have hε'μ : ε' ≤ μ / τ₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε'ε : ε' ≤ ε / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  set s₀ : ℕ := ⌈2 * ((K : ℝ) + 1) / (1 - τ * heightSlope)⌉₊ + 1 with hs₀
  have hd1 : LogDens0 (fun n => ε' * Nat.size (TaoCollatz.oddPart n) < padicValNat 2 n) :=
    logDens0_of_summable (summableLargeTwoAdic ε' hε')
  have hd2 : LogDens0 (fun n => n ≤ 2 ^ (2 * s₀)) := logDens0_of_bdd (fun n h => h)
  have hd3 : LogDens0 (fun n => ¬ GoodOddUpTo δ τ (TaoCollatz.oddPart n)) :=
    logDens0OddPart (fun m => ¬ GoodOddUpTo δ τ m)
      (logDens0OfWindow (fun m => ¬ GoodOddUpTo δ τ m)
        (goodOddUpTo_whp hτ0 (by linarith) hδ))
  refine ((hd1.or hd2).or hd3).mono fun n hn => ?_
  by_contra hcon
  simp only [not_or, not_lt, not_le, not_not] at hcon
  obtain ⟨⟨ha, hn2⟩, hgood⟩ := hcon
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn2
  obtain ⟨a, ha_def⟩ : ∃ a, a = padicValNat 2 n := ⟨_, rfl⟩
  obtain ⟨m, hm_def⟩ : ∃ m, m = TaoCollatz.oddPart n := ⟨_, rfl⟩
  rw [← ha_def, ← hm_def] at ha
  rw [← hm_def] at hgood
  have hm : m % 2 = 1 := hm_def ▸ TaoCollatz.oddPart_odd hn0
  have hm1 : 1 ≤ m := by omega
  have hnm : 2 ^ a * m = n := by rw [ha_def, hm_def]; exact TaoCollatz.two_pow_mul_oddPart n
  have hsnn : (0 : ℝ) ≤ Nat.size m := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have haε' : (a : ℝ) ≤ ε' * Nat.size m := ha
  have has : (a : ℝ) ≤ Nat.size m := by
    have := mul_le_mul_of_nonneg_right hε'1 hsnn
    linarith
  have haμ : τ₁ * a ≤ μ * Nat.size m := by
    have h := mul_le_mul_of_nonneg_left (le_trans haε' (mul_le_mul_of_nonneg_right hε'μ hsnn))
      (by linarith : (0 : ℝ) ≤ τ₁)
    have he : τ₁ * (μ / τ₁ * Nat.size m) = μ * Nat.size m := by
      field_simp
    linarith
  have haε : (a : ℝ) ≤ ε / 4 * Nat.size m :=
    le_trans haε' (mul_le_mul_of_nonneg_right hε'ε hsnn)
  have has' : a ≤ Nat.size m := by exact_mod_cast has
  have hsize : s₀ ≤ Nat.size m := by
    by_contra hlt
    push Not at hlt
    have hm2 : m < 2 ^ s₀ := lt_of_lt_of_le (Nat.lt_size_self m) (Nat.pow_le_pow_right (by norm_num)
      hlt.le)
    have ha2 : 2 ^ a ≤ 2 ^ s₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : n < 2 ^ (2 * s₀) := by
      rw [← hnm, two_mul, pow_add]
      exact Nat.mul_lt_mul_of_le_of_lt ha2 hm2 (by positivity)
    omega
  have hs1 : 1 ≤ Nat.size m := le_trans (by omega) hsize
  have hsγ : 2 * ((K : ℝ) + 1) ≤ (1 - τ * heightSlope) * Nat.size m := by
    have h := Nat.le_ceil (2 * ((K : ℝ) + 1) / (1 - τ * heightSlope))
    rw [div_le_iff₀ hγ] at h
    have hc : (⌈2 * ((K : ℝ) + 1) / (1 - τ * heightSlope)⌉₊ : ℝ) ≤ Nat.size m := by
      have : ⌈2 * ((K : ℝ) + 1) / (1 - τ * heightSlope)⌉₊ ≤ Nat.size m := by omega
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_right hc hγ.le
    linarith
  have hτa : τ₁ * (Nat.size m + a) - a ≤ τ * Nat.size m := by rw [hτdef]; linarith
  rw [← hnm] at hn
  exact not_badHeight_two_pow_mul hτ0.le hδ.le hε hδγ (min_le_right _ _) hK hm1 hs1 hsγ hτa haε
    hgood hn

/-- **The height line through every `τ < 1 / β`.**  From `heightLawUpTo_of_one_le` at
`max τ 4`, since `4 β < 1`. -/
theorem heightLawBelowThreshold : HeightLawBelowThreshold := by
  intro τ hτ
  have hβ := heightSlope_pos
  have hβ5 := heightSlope_le
  refine (heightLawUpTo_of_one_le (le_trans (by norm_num) (le_max_right τ 4)) ?_).mono
    (le_max_left τ 4)
  rcases le_total τ 4 with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    exact hτ

/-- **`C* = 1 / β` is the sharp end of the height line.** -/
theorem heightLawUpTo_iff {τ : ℝ} (hτ : τ * heightSlope ≠ 1) :
    HeightLawUpTo τ ↔ τ * heightSlope < 1 :=
  ⟨fun h => lt_of_le_of_ne (not_lt.mp fun hgt => not_heightLawUpTo_of_gt hgt h) hτ,
    fun h => heightLawBelowThreshold τ h⟩

/-- **First passage below `n^θ`, for every `0 < θ < 1`.**  From `heightLawBelowThreshold` at
`τ = (1 − θ) / β + η`, by the proof of `firstPassage_law`. -/
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
