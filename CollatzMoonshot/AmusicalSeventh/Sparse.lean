/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalChains

/-!
# Quantitative infrastructure for sparse sweeping

This file begins the quantitative replacement for the deliberately large `windowBound` used in
`AmusicalWindow`.  The elementary bounds below control every forward and backward affine offset
on a representative modulo `12^L`; they are the first input to the residue-order lemma used by
`sparse_sweep`.
-/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- On the nonnegative integers, one step in either direction is at most `z ↦ 2z+1`. -/
theorem amusical_max_step {z : ℤ} (hz : 0 ≤ z) :
    amusical z ≤ 2 * z + 1 ∧ amusicalInv z ≤ 2 * z + 1 := by
  constructor
  · unfold amusical
    split_ifs <;> omega
  · unfold amusicalInv
    split_ifs <;> omega

/-- Uniform exponential bound for a forward orbit segment starting at a nonnegative integer. -/
theorem amusical_iterate_lt_two_pow_mul {z : ℤ} (hz : 0 ≤ z) (t : ℕ) :
    amusical^[t] z < (2 : ℤ) ^ t * (z + 1) := by
  induction t generalizing z with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply]
      have hz' : 0 ≤ amusical z := amusical_nonneg hz
      have hih := ih hz'
      have hstep := (amusical_max_step hz).1
      rw [pow_succ]
      nlinarith [show (0 : ℤ) < 2 ^ t by positivity]

/-- Uniform exponential bound for a backward orbit segment starting at a nonnegative integer. -/
theorem amusicalInv_iterate_lt_two_pow_mul {z : ℤ} (hz : 0 ≤ z) (t : ℕ) :
    amusicalInv^[t] z < (2 : ℤ) ^ t * (z + 1) := by
  induction t generalizing z with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply]
      have hz' : 0 ≤ amusicalInv z := amusicalInv_nonneg hz
      have hih := ih hz'
      have hstep := (amusical_max_step hz).2
      rw [pow_succ]
      nlinarith [show (0 : ℤ) < 2 ^ t by positivity]

/-- Every length-`L` forward and backward segment from a representative modulo `12^L` stays
below `24^L`.  This explicit bound is what makes window order a finite residue condition at an
exponential threshold. -/
theorem amusical_window_representative_lt {L t c : ℕ} (ht : t ≤ L) (hc : c < 12 ^ L) :
    amusical^[t] (c : ℤ) < 24 ^ L ∧ amusicalInv^[t] (c : ℤ) < 24 ^ L := by
  have hc1 : c + 1 ≤ 12 ^ L := by omega
  have hp : 2 ^ t ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) ht
  have hprod : 2 ^ t * (c + 1) ≤ 24 ^ L := by
    calc
      2 ^ t * (c + 1) ≤ 2 ^ L * 12 ^ L := Nat.mul_le_mul hp hc1
      _ = 24 ^ L := by rw [← Nat.mul_pow]
  constructor
  · exact lt_of_lt_of_le (amusical_iterate_lt_two_pow_mul (Int.natCast_nonneg c) t)
      (by exact_mod_cast hprod)
  · exact lt_of_lt_of_le (amusicalInv_iterate_lt_two_pow_mul (Int.natCast_nonneg c) t)
      (by exact_mod_cast hprod)

/-- **Lemma W.** Above `2 · 324^L`, being an `L`-window minimum is determined by the
forward and backward branch words, hence by the residue modulo `12^L`. -/
theorem isWindowMin_iff_words_of_ge (L n : ℕ) (hn : 2 * 324 ^ L ≤ n) :
    IsWindowMin L n ↔ FwdGood L (amusicalForwardWord L n) ∧
      BwdGood L (amusicalBackwardWord L n) := by
  set M := 12 ^ L with hM
  have hMpos : 0 < M := by positivity
  set c := n % M with hc
  set q := n / M with hq
  have hcM : c < M := Nat.mod_lt _ hMpos
  have hpow : M * (24 ^ L + 1) ≤ 2 * 324 ^ L := by
    have h288 : 288 ^ L ≤ 324 ^ L := Nat.pow_le_pow_left (by omega) L
    have h12 : 12 ^ L ≤ 324 ^ L := Nat.pow_le_pow_left (by omega) L
    calc
      M * (24 ^ L + 1) = 288 ^ L + 12 ^ L := by
        rw [hM, mul_add, mul_one, ← Nat.mul_pow]
      _ ≤ 324 ^ L + 324 ^ L := Nat.add_le_add h288 h12
      _ = 2 * 324 ^ L := by omega
  have hqge : 24 ^ L + 1 ≤ q := by
    apply (Nat.le_div_iff_mul_le hMpos).mpr
    rw [mul_comm]
    exact le_trans hpow hn
  have hnq : (n : ℤ) = c + M * q := by
    have h := Nat.mod_add_div n M
    exact_mod_cast h.symm
  have hMsplit : M = 4 ^ L * 3 ^ L := by
    rw [hM, ← Nat.mul_pow]
  have hnF : (n : ℤ) = c + 4 ^ L * (3 ^ L * q) := by
    rw [hnq, hMsplit]
    push_cast
    ring
  have hnB : (n : ℤ) = c + 3 ^ L * (4 ^ L * q) := by
    rw [hnq, hMsplit]
    push_cast
    ring
  have hpatF : amusicalForwardWord L n = amusicalForwardWord L c := by
    rw [hnF, amusicalForwardWord_add_pow_four_mul]
  have hpatB : amusicalBackwardWord L n = amusicalBackwardWord L c := by
    rw [hnB, amusicalBackwardWord_add_pow_three_mul]
  rw [hpatF, hpatB]
  have hf0 : ∀ t, 0 ≤ amusical^[t] (c : ℤ) := by
    intro t
    induction t with
    | zero => simpa using (Int.natCast_nonneg c)
    | succ t ih => rw [Function.iterate_succ_apply']; exact amusical_nonneg ih
  have hb0 : ∀ t, 0 ≤ amusicalInv^[t] (c : ℤ) := by
    intro t
    induction t with
    | zero => simpa using (Int.natCast_nonneg c)
    | succ t ih => rw [Function.iterate_succ_apply']; exact amusicalInv_nonneg ih
  have hbound : ∀ t, t ≤ L → |amusical^[t] (c : ℤ) - c| < q ∧
      |amusicalInv^[t] (c : ℤ) - c| < q := by
    intro t ht
    have hc12 : c < 12 ^ L := by simpa [hM] using hcM
    have hb := amusical_window_representative_lt ht hc12
    have hq24 : (24 : ℤ) ^ L < q := by exact_mod_cast (show 24 ^ L < q by omega)
    have hc24 : (c : ℤ) < 24 ^ L := by
      exact_mod_cast (lt_of_lt_of_le hc12 (Nat.pow_le_pow_left (by omega) L))
    constructor
    · rw [abs_lt]
      constructor
      · have := hf0 t; omega
      · omega
    · rw [abs_lt]
      constructor
      · have := hb0 t; omega
      · omega
  have hq3 : (q : ℤ) ≤ 3 ^ L * q :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hq4 : (q : ℤ) ≤ 4 ^ L * q :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hF : ∀ t, 1 ≤ t → t ≤ L → ((n : ℤ) ≤ amusical^[t] n ↔
      2 ^ (t + ((Finset.univ.filter fun i : Fin L =>
        i.val < t ∧ amusicalForwardWord L c i = true).card)) < 3 ^ t) := by
    intro t ht1 ht
    rw [hnF, amusical_iterate_add_pow_four_mul_slope L t ht]
    rw [show (4 : ℤ) ^ (L - t) * 3 ^ t * 2 ^ amusicalForwardEvenCount t c * (3 ^ L * q) =
      (4 ^ (L - t) * 3 ^ t * 2 ^ amusicalForwardEvenCount t c) * (3 ^ L * q) by ring]
    rw [add_mul_le_add_mul_iff
      (amusical_forward_slope_ne L t (amusicalForwardEvenCount t c) ht1)
      (lt_of_lt_of_le (hbound t ht).1 hq3)]
    exact amusical_forward_slope_lt_iff L t _ _ ht
      (amusicalForwardWord_true_card_add_evenCount L t ht c)
  have hB : ∀ t, 1 ≤ t → t ≤ L → ((n : ℤ) ≤ amusicalInv^[t] n ↔
      3 ^ t < 2 ^ (t + ((Finset.univ.filter fun i : Fin L =>
        i.val < t ∧ amusicalBackwardWord L c i = true).card))) := by
    intro t ht1 ht
    rw [hnB, amusicalInv_iterate_add_pow_three_mul_slope L t ht]
    rw [add_mul_le_add_mul_iff
      (amusical_backward_slope_ne L t (amusicalBackwardFourCount t c) ht1 ht)
      (lt_of_lt_of_le (hbound t ht).2 hq4)]
    rw [amusicalBackwardWord_true_card_eq_fourCount L t ht c]
    exact amusical_backward_slope_lt_iff L t _ ht
  unfold IsWindowMin
  constructor
  · intro h
    exact ⟨fun t h1 h2 => (hF t h1 h2).mp (h t h1 h2).1,
      fun t h1 h2 => (hB t h1 h2).mp (h t h1 h2).2⟩
  · rintro ⟨h1, h2⟩ t ht1 ht2
    exact ⟨(hF t ht1 ht2).mpr (h1 t ht1 ht2),
      (hB t ht1 ht2).mpr (h2 t ht1 ht2)⟩

/-- Every finite centered orbit window has a minimizing offset.  This is the deterministic
selection underlying the exceptional-offset count in Lemma T. -/
theorem exists_centered_window_minimizer (L : ℕ) (n : ℤ) :
    ∃ t : ℤ, |t| ≤ L ∧ ∀ s : ℤ, |s| ≤ L →
      (amusicalPerm ^ t) n ≤ (amusicalPerm ^ s) n := by
  let I := Finset.Icc (-(L : ℤ)) (L : ℤ)
  have hI : I.Nonempty := ⟨0, by simp [I]⟩
  obtain ⟨t, htI, htmin⟩ := Finset.exists_min_image I (fun s => (amusicalPerm ^ s) n) hI
  refine ⟨t, ?_, ?_⟩
  · simpa [I, abs_le] using htI
  · intro s hs
    apply htmin s
    simpa [I, abs_le] using hs

/-- If a minimum of the centered `L`-window occurs within `K` steps of its center, the
corresponding orbit point is an `(L-K)`-window minimum. -/
theorem isWindowMin_sub_of_centered_minimizer {L K : ℕ} {n : ℤ} {t : ℤ}
    (hK : K ≤ L) (ht : |t| ≤ K)
    (hmin : ∀ s : ℤ, |s| ≤ L → (amusicalPerm ^ t) n ≤ (amusicalPerm ^ s) n) :
    IsWindowMin (L - K) ((amusicalPerm ^ t) n) := by
  intro u hu1 huLK
  have hu : (u : ℤ) ≤ L - K := by exact_mod_cast huLK
  have ht_bounds := abs_le.mp ht
  have hplus : |t + (u : ℤ)| ≤ L := by
    rw [abs_le]
    constructor <;> push_cast at ht_bounds hu ⊢ <;> omega
  have hminus : |t - (u : ℤ)| ≤ L := by
    rw [abs_le]
    constructor <;> push_cast at ht_bounds hu ⊢ <;> omega
  constructor
  · rw [amusical_iterate_eq_perm_pow, ← Equiv.Perm.mul_apply, ← zpow_add]
    exact hmin _ (by simpa [add_comm] using hplus)
  · rw [amusicalInv_iterate_eq_perm_pow, ← Equiv.Perm.mul_apply, ← zpow_add]
    exact hmin _ (by simpa [sub_eq_add_neg, add_comm] using hminus)

end CollatzMoonshot.Amusical
