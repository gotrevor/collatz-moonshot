/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawDensity

/-!
# The orbit word law: even starts

`notBadStartOfGoodOdd_holds` proves `NotBadStartOfGoodOdd`.  The letters of `2^a m` are `a` zeros
followed by the letters of `m`, so the count of `u` among the first `N = C size (2^a m)` letters of
`2^a m` differs from the count among the first `N − a` letters of `m` by at most `a + |u|`
(`card_badStart_le`, `wcnt_le_card_badStart`).  For `C ≤ 4` and `15 a ≤ size m`, those are within
`4.2 size m` letters of `m`, where `m` is good.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-- `size (2^a m) = size m + a`, for `m ≠ 0`. -/
theorem size_two_pow_mul {m : ℕ} (hm : m ≠ 0) (a : ℕ) : Nat.size (2 ^ a * m) = Nat.size m + a := by
  rw [mul_comm, ← Nat.shiftLeft_eq, Nat.size_shiftLeft hm]

/-- Halving `2^a m` `a` times gives `m`. -/
theorem tstep_iterate_two_pow_mul (a m : ℕ) : tstep^[a] (2 ^ a * m) = m := by
  rw [tstep_iterate_of_dvd a _ (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (by positivity)]

/-- The letters of `2^a m` at positions `[a, N)` are those of `m` at `[0, N − a)`. -/
theorem card_Ico_filter_eq_wcnt (u : List Bool) (a m N : ℕ) :
    ((Finset.Ico a N).filter
      fun i => WindowMatch (fun s => u.getD s false) u.length i (2 ^ a * m)).card =
      wcnt u m 0 (N - a) := by
  have h := wcnt_shift u (2 ^ a * m) a 0 (N - a)
  rw [add_zero, tstep_iterate_two_pow_mul] at h
  rw [← h, wcnt]
  congr 2
  rcases le_or_gt a N with haN | haN
  · rw [Nat.add_sub_cancel' haN]
  · rw [Nat.sub_eq_zero_of_le haN.le, add_zero, Finset.Ico_self,
      Finset.Ico_eq_empty_of_le haN.le]

/-- The count in `BadStart` is at most `a` more than the count of `m`. -/
theorem card_badStart_le (u : List Bool) (a m N : ℕ) :
    ((Finset.range N).filter fun i => i + u.length ≤ N ∧
      WindowMatch (fun s => u.getD s false) u.length i (2 ^ a * m)).card ≤
      a + wcnt u m 0 (N - a) := by
  rw [← card_Ico_filter_eq_wcnt]
  refine le_trans (Finset.card_le_card (t := Finset.range a ∪ (Finset.Ico a N).filter
    fun i => WindowMatch (fun s => u.getD s false) u.length i (2 ^ a * m)) fun i hi => ?_)
    (le_trans (Finset.card_union_le _ _) (by rw [Finset.card_range]))
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hi ⊢
  rcases lt_or_ge i a with h | h
  · exact Or.inl h
  · exact Or.inr ⟨⟨h, hi.1⟩, hi.2.2⟩

/-- The count of `m` is at most `|u|` more than the count in `BadStart`. -/
theorem wcnt_le_card_badStart (u : List Bool) (a m N : ℕ) :
    wcnt u m 0 (N - a) ≤
      ((Finset.range N).filter fun i => i + u.length ≤ N ∧
        WindowMatch (fun s => u.getD s false) u.length i (2 ^ a * m)).card + u.length := by
  rw [← card_Ico_filter_eq_wcnt]
  refine le_trans (Finset.card_le_card (t := ((Finset.range N).filter fun i => i + u.length ≤ N ∧
      WindowMatch (fun s => u.getD s false) u.length i (2 ^ a * m)) ∪ Finset.Ico (N - u.length) N)
    fun i hi => ?_) (le_trans (Finset.card_union_le _ _) ?_)
  · simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hi ⊢
    rcases le_or_gt (i + u.length) N with h | h
    · exact Or.inl ⟨hi.1.2, h, hi.2⟩
    · exact Or.inr ⟨by omega, hi.1.2⟩
  · rw [Nat.card_Ico]
    omega

/-- **The even reduction** (`NotBadStartOfGoodOdd`). -/
theorem notBadStartOfGoodOdd_holds : NotBadStartOfGoodOdd := by
  intro C hC4 u δ hδ
  refine ⟨⌈4 * u.length / δ⌉₊, fun a m hm hs h15 h8 hgood hbad => ?_⟩
  have hm0 : m ≠ 0 := by omega
  set s := Nat.size m with hsdef
  unfold BadStart at hbad
  rw [size_two_pow_mul hm0] at hbad
  set N := C * (s + a) with hN
  set S := ((Finset.range N).filter fun i => i + u.length ≤ N ∧
    WindowMatch (fun s => u.getD s false) u.length i (2 ^ a * m)).card with hS
  have h1 : (S : ℝ) ≤ a + wcnt u m 0 (N - a) := by exact_mod_cast card_badStart_le u a m N
  have h2 : (wcnt u m 0 (N - a) : ℝ) ≤ S + u.length := by
    exact_mod_cast wcnt_le_card_badStart u a m N
  have hT : 5 * (N - a) ≤ 21 * s := by
    have : N ≤ 4 * (s + a) := Nat.mul_le_mul_right _ hC4
    omega
  have h3 := hgood (N - a) hT
  set p : ℝ := (1 / 2 : ℝ) ^ u.length with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h4 : |((N - a : ℕ) : ℝ) * p - (N : ℝ) * p| ≤ a := by
    rcases le_or_gt a N with haN | haN
    · rw [Nat.cast_sub haN, ← sub_mul, sub_sub_cancel_left, neg_mul, abs_neg,
        abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) hp1
    · rw [Nat.sub_eq_zero_of_le haN.le, Nat.cast_zero, zero_mul, zero_sub, abs_neg,
        abs_of_nonneg (by positivity)]
      have : (N : ℝ) ≤ a := by exact_mod_cast haN.le
      nlinarith
  have hwdev : wdev u m 0 (N - a) = (wcnt u m 0 (N - a) : ℝ) - ((N - a : ℕ) : ℝ) * p := rfl
  have hsu : (u.length : ℝ) ≤ δ * s / 4 := by
    have h := Nat.le_ceil (4 * u.length / δ)
    have h' : (⌈4 * u.length / δ⌉₊ : ℝ) ≤ s := by exact_mod_cast hs
    have h'' : 4 * (u.length : ℝ) / δ ≤ s := le_trans h h'
    rw [div_le_iff₀ hδ] at h''
    linarith
  have hdev : |(S : ℝ) - (N : ℝ) * p| ≤ a + u.length + δ / 2 * s + a := by
    rw [abs_le] at h3 h4 ⊢
    constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
  have hsa : (s : ℝ) ≤ ((s + a : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  have : δ * ((s + a : ℕ) : ℝ) < |(S : ℝ) - (N : ℝ) * p| := by
    simpa [hS, hp, hN] using hbad
  have hδs : δ * (s : ℝ) ≤ δ * ((s + a : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hsa hδ.le
  linarith

end CollatzMoonshot.Conjugacy
