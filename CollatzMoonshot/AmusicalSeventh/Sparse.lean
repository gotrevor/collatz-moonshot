/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalChains
import CollatzMoonshot.AmusicalSeventh.Rewire

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

/-- A forward slope descent occurs when the marked-letter product makes the affine slope less
than one. -/
abbrev FwdSlopeDescends (L : ℕ) (w : Fin L → Bool) : Prop :=
  3 ^ L < 2 ^ (L + latticeMarked w)

/-- A backward slope descent is the reverse marked-letter inequality. -/
abbrev BwdSlopeDescends (L : ℕ) (w : Fin L → Bool) : Prop :=
  2 ^ (L + latticeMarked w) < 3 ^ L

/-- Above the Lemma W threshold, each individual forward and backward comparison is determined
by the corresponding prefix of the branch word. -/
theorem iterate_le_iff_words_of_ge (L n : ℕ) (hn : 2 * 324 ^ L ≤ n) :
    (∀ t, 1 ≤ t → t ≤ L → ((n : ℤ) ≤ amusical^[t] n ↔
      2 ^ (t + ((Finset.univ.filter fun i : Fin L =>
        i.val < t ∧ amusicalForwardWord L n i = true).card)) < 3 ^ t)) ∧
    (∀ t, 1 ≤ t → t ≤ L → ((n : ℤ) ≤ amusicalInv^[t] n ↔
      3 ^ t < 2 ^ (t + ((Finset.univ.filter fun i : Fin L =>
        i.val < t ∧ amusicalBackwardWord L n i = true).card)))) := by
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
  exact ⟨hF, hB⟩

/-- **Lemma W.** Above `2 · 324^L`, being an `L`-window minimum is determined by the
forward and backward branch words, hence by the residue modulo `12^L`. -/
theorem isWindowMin_iff_words_of_ge (L n : ℕ) (hn : 2 * 324 ^ L ≤ n) :
    IsWindowMin L n ↔ FwdGood L (amusicalForwardWord L n) ∧
      BwdGood L (amusicalBackwardWord L n) := by
  obtain ⟨hF, hB⟩ := iterate_le_iff_words_of_ge L n hn
  unfold IsWindowMin
  constructor
  · intro h
    exact ⟨fun t h1 h2 => (hF t h1 h2).mp (h t h1 h2).1,
      fun t h1 h2 => (hB t h1 h2).mp (h t h1 h2).2⟩
  · rintro ⟨h1, h2⟩ t ht1 ht2
    exact ⟨(hF t ht1 ht2).mpr (h1 t ht1 ht2),
      (hB t ht1 ht2).mpr (h2 t ht1 ht2)⟩

/-- At the Lemma W threshold, a forward descent is exactly a descending forward slope. -/
theorem iterate_lt_iff_fwdSlopeDescends_of_ge (L n : ℕ) (hL : 1 ≤ L)
    (hn : 2 * 324 ^ L ≤ n) :
    amusical^[L] (n : ℤ) < n ↔ FwdSlopeDescends L (amusicalForwardWord L n) := by
  rw [show amusical^[L] (n : ℤ) < n ↔ ¬ (n : ℤ) ≤ amusical^[L] n by omega]
  rw [(iterate_le_iff_words_of_ge L n hn).1 L hL le_rfl]
  have hcard : (Finset.univ.filter fun i : Fin L =>
      i.val < L ∧ amusicalForwardWord L n i = true).card =
      latticeMarked (amusicalForwardWord L n) := by
    simp [latticeMarked]
  rw [hcard]
  unfold FwdSlopeDescends
  have hne : 3 ^ L ≠ 2 ^ (L + latticeMarked (amusicalForwardWord L n)) := by
    have ho : Odd (3 ^ L) := (by norm_num : Odd 3).pow
    have he : Even (2 ^ (L + latticeMarked (amusicalForwardWord L n))) :=
      Nat.even_pow.mpr ⟨by decide, by omega⟩
    rcases ho with ⟨a, ha⟩
    rcases he with ⟨b, hb⟩
    omega
  omega

/-- At the Lemma W threshold, a backward descent is exactly a descending backward slope. -/
theorem inv_iterate_lt_iff_bwdSlopeDescends_of_ge (L n : ℕ) (hL : 1 ≤ L)
    (hn : 2 * 324 ^ L ≤ n) :
    amusicalInv^[L] (n : ℤ) < n ↔ BwdSlopeDescends L (amusicalBackwardWord L n) := by
  rw [show amusicalInv^[L] (n : ℤ) < n ↔ ¬ (n : ℤ) ≤ amusicalInv^[L] n by omega]
  rw [(iterate_le_iff_words_of_ge L n hn).2 L hL le_rfl]
  have hcard : (Finset.univ.filter fun i : Fin L =>
      i.val < L ∧ amusicalBackwardWord L n i = true).card =
      latticeMarked (amusicalBackwardWord L n) := by
    simp [latticeMarked]
  rw [hcard]
  unfold BwdSlopeDescends
  have hne : 3 ^ L ≠ 2 ^ (L + latticeMarked (amusicalBackwardWord L n)) := by
    have ho : Odd (3 ^ L) := (by norm_num : Odd 3).pow
    have he : Even (2 ^ (L + latticeMarked (amusicalBackwardWord L n))) :=
      Nat.even_pow.mpr ⟨by decide, by omega⟩
    rcases ho with ⟨a, ha⟩
    rcases he with ⟨b, hb⟩
    omega
  omega

/-! ## Chernoff bounds for one-sided descents -/

/-- The common Chernoff weight for forward and backward branch words.  An unmarked letter has
normalized weight `1 / √6`, while a marked letter has normalized weight `1 / √3`. -/
noncomputable def descentChernoffWeight {L : ℕ} (w : Fin L → Bool) : ℝ :=
  (1 / Real.sqrt 6) ^ latticeUnmarked w *
    (1 / Real.sqrt 3) ^ latticeMarked w

/-- The exponential rate in the one-sided descent bounds. -/
noncomputable def descentChernoffRate : ℝ :=
  1 / Real.sqrt 6 + 1 / Real.sqrt 3

theorem sum_bool_cons_real {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ w, f w = ∑ b : Bool, ∑ u : Fin n → Bool, f (Fin.cons b u) := by
  refine ((Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool))
    (fun x => f (Fin.cons x.1 x.2)) f (fun _ => rfl)).symm).trans ?_
  exact Fintype.sum_prod_type _

theorem descentChernoffWeight_cons_false {n : ℕ} (u : Fin n → Bool) :
    descentChernoffWeight (Fin.cons false u) =
      (1 / Real.sqrt 6) * descentChernoffWeight u := by
  simp only [descentChernoffWeight, latticeMarked_cons, latticeUnmarked_cons,
    Bool.false_eq_true, ↓reduceIte, zero_add]
  rw [show 1 + latticeUnmarked u = latticeUnmarked u + 1 by omega, pow_succ]
  ring

theorem descentChernoffWeight_cons_true {n : ℕ} (u : Fin n → Bool) :
    descentChernoffWeight (Fin.cons true u) =
      (1 / Real.sqrt 3) * descentChernoffWeight u := by
  simp only [descentChernoffWeight, latticeMarked_cons, latticeUnmarked_cons,
    ↓reduceIte, zero_add]
  rw [show 1 + latticeMarked u = latticeMarked u + 1 by omega, pow_succ]
  ring

/-- The Chernoff weights of all Boolean words of length `L` have total mass `ρ^L`. -/
theorem sum_descentChernoffWeight (L : ℕ) :
    ∑ w : Fin L → Bool, descentChernoffWeight w = descentChernoffRate ^ L := by
  unfold descentChernoffRate
  induction L with
  | zero => simp [descentChernoffWeight, latticeMarked, latticeUnmarked]
  | succ L ih =>
      rw [sum_bool_cons_real, Fintype.sum_bool]
      simp_rw [descentChernoffWeight_cons_false, descentChernoffWeight_cons_true]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ih, pow_succ]
      ring

/-- A convenient rational upper bound for the exact Chernoff rate
`ρ = 1 / √6 + 1 / √3`. -/
theorem descentChernoffRate_lt_ninetyNineHundredths :
    descentChernoffRate < (99 : ℝ) / 100 := by
  unfold descentChernoffRate
  have hs6 : (61 : ℝ) / 25 < Real.sqrt 6 := by
    rw [← sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg _)]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hs3 : (173 : ℝ) / 100 < Real.sqrt 3 := by
    rw [← sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg _)]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hi6 : 1 / Real.sqrt 6 < (25 : ℝ) / 61 := by
    have hi := one_div_lt_one_div_of_lt (by positivity) hs6
    norm_num at hi ⊢
    exact hi
  have hi3 : 1 / Real.sqrt 3 < (100 : ℝ) / 173 := by
    have hi := one_div_lt_one_div_of_lt (by positivity) hs3
    norm_num at hi ⊢
    exact hi
  linarith

theorem descentChernoffWeight_sq {L : ℕ} (w : Fin L → Bool) :
    descentChernoffWeight w ^ 2 =
      (1 / 6 : ℝ) ^ latticeUnmarked w *
        (1 / 3 : ℝ) ^ latticeMarked w := by
  unfold descentChernoffWeight
  rw [mul_pow]
  rw [show ((1 / Real.sqrt 6 : ℝ) ^ latticeUnmarked w) ^ 2 =
      ((1 / Real.sqrt 6 : ℝ) ^ 2) ^ latticeUnmarked w by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
  rw [show ((1 / Real.sqrt 3 : ℝ) ^ latticeMarked w) ^ 2 =
      ((1 / Real.sqrt 3 : ℝ) ^ 2) ^ latticeMarked w by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
  norm_num [Real.sq_sqrt]

theorem latticeMarked_add_unmarked {L : ℕ} (w : Fin L → Bool) :
    latticeMarked w + latticeUnmarked w = L := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin L))) (fun i => w i = true)
  simpa [latticeMarked, latticeUnmarked] using h

/-- If a forward word has descending affine slope, its uniform word mass is strictly below its
Chernoff weight. -/
theorem fwdSlopeDescends_weight_lt {L : ℕ} (w : Fin L → Bool)
    (h : 3 ^ L < 2 ^ (L + latticeMarked w)) :
    (1 / (2 : ℝ) ^ L) < descentChernoffWeight w := by
  set a := latticeMarked w
  set b := latticeUnmarked w
  have hab : a + b = L := by simpa [a, b] using latticeMarked_add_unmarked w
  have hden : 6 ^ b * 3 ^ a < 4 ^ L := by
    calc
      6 ^ b * 3 ^ a = 2 ^ b * 3 ^ L := by
        rw [show 6 = 2 * 3 by norm_num, mul_pow]
        calc
          2 ^ b * 3 ^ b * 3 ^ a = 2 ^ b * (3 ^ b * 3 ^ a) := by ring
          _ = 2 ^ b * 3 ^ (b + a) := by rw [pow_add]
          _ = 2 ^ b * 3 ^ L := by congr 2; omega
      _ < 2 ^ b * 2 ^ (L + a) :=
        Nat.mul_lt_mul_of_pos_left h (by positivity)
      _ = 4 ^ L := by
        rw [← pow_add, show b + (L + a) = 2 * L by omega, pow_mul]
        norm_num
  rw [← sq_lt_sq₀ (by positivity) (by unfold descentChernoffWeight; positivity)]
  rw [show descentChernoffWeight w ^ 2 =
      (1 / 6 : ℝ) ^ b * (1 / 3 : ℝ) ^ a by
        simpa [a, b] using descentChernoffWeight_sq w]
  have hdenR : (6 : ℝ) ^ b * 3 ^ a < 4 ^ L := by exact_mod_cast hden
  calc
    (1 / (2 : ℝ) ^ L) ^ 2 = 1 / (4 : ℝ) ^ L := by
      rw [div_pow]
      congr 1
      · norm_num
      · rw [← pow_mul, Nat.mul_comm L 2, pow_mul]
        norm_num
    _ < 1 / ((6 : ℝ) ^ b * 3 ^ a) :=
      one_div_lt_one_div_of_lt (by positivity) hdenR
    _ = (1 / 6 : ℝ) ^ b * (1 / 3 : ℝ) ^ a := by
      norm_num [div_pow]
      ring

/-- If a backward word has descending affine slope, its normalized residue-fiber mass is strictly
below its Chernoff weight. -/
theorem bwdSlopeDescends_weight_lt {L : ℕ} (w : Fin L → Bool)
    (h : 2 ^ (L + latticeMarked w) < 3 ^ L) :
    (2 : ℝ) ^ latticeMarked w / 3 ^ L < descentChernoffWeight w := by
  set a := latticeMarked w
  set b := latticeUnmarked w
  have hab : a + b = L := by simpa [a, b] using latticeMarked_add_unmarked w
  have hcross : 4 ^ a * (6 ^ b * 3 ^ a) < 9 ^ L := by
    calc
      4 ^ a * (6 ^ b * 3 ^ a) = 2 ^ (2 * a + b) * 3 ^ (b + a) := by
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul]
        rw [show 6 = 2 * 3 by norm_num, mul_pow, pow_add, pow_add]
        ring
      _ = 2 ^ (L + a) * 3 ^ L := by congr 2 <;> omega
      _ < 3 ^ L * 3 ^ L := Nat.mul_lt_mul_of_pos_right h (by positivity)
      _ = 9 ^ L := by rw [← mul_pow]; norm_num
  rw [← sq_lt_sq₀ (by positivity) (by unfold descentChernoffWeight; positivity)]
  rw [show descentChernoffWeight w ^ 2 =
      (1 / 6 : ℝ) ^ b * (1 / 3 : ℝ) ^ a by
        simpa [a, b] using descentChernoffWeight_sq w]
  have hcrossR : (4 : ℝ) ^ a * ((6 : ℝ) ^ b * 3 ^ a) < 9 ^ L := by
    exact_mod_cast hcross
  calc
    ((2 : ℝ) ^ a / 3 ^ L) ^ 2 = 4 ^ a / 9 ^ L := by
      rw [div_pow]
      congr 1
      · rw [← pow_mul, Nat.mul_comm a 2, pow_mul]
        norm_num
      · rw [← pow_mul, Nat.mul_comm L 2, pow_mul]
        norm_num
    _ < 1 / ((6 : ℝ) ^ b * 3 ^ a) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      simpa using hcrossR
    _ = (1 / 6 : ℝ) ^ b * (1 / 3 : ℝ) ^ a := by
      norm_num [div_pow]
      ring

/-- Generic fiber count for a predicate on forward branch words. -/
theorem count_amusicalForwardWord_pred (L : ℕ) (P : (Fin L → Bool) → Prop)
    [DecidablePred P] :
    Nat.count (fun r : ℕ => P (amusicalForwardWord L r)) (4 ^ L) =
      ∑ w : Fin L → Bool, if P w then 2 ^ L else 0 := by
  classical
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_sum_card_fiberwise
    (f := fun r : ℕ => amusicalForwardWord L r) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.filter_filter]
  split_ifs with hw
  · rw [← count_amusicalForwardWord_eq L w, Nat.count_eq_card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro r _
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hw, h⟩⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro r _ ⟨h1, h2⟩
    exact hw (h2 ▸ h1)

/-- Generic fiber count for a predicate on backward branch words. -/
theorem count_amusicalBackwardWord_pred (L : ℕ) (P : (Fin L → Bool) → Prop)
    [DecidablePred P] :
    Nat.count (fun r : ℕ => P (amusicalBackwardWord L r)) (3 ^ L) =
      ∑ w : Fin L → Bool, if P w then 2 ^ latticeMarked w else 0 := by
  classical
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_sum_card_fiberwise
    (f := fun r : ℕ => amusicalBackwardWord L r) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.filter_filter]
  split_ifs with hw
  · rw [show latticeMarked w =
      (Finset.univ.filter fun i : Fin L => w i = true).card by rfl]
    rw [← count_amusicalBackwardWord_eq L w, Nat.count_eq_card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro r _
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hw, h⟩⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro r _ ⟨h1, h2⟩
    exact hw (h2 ▸ h1)

theorem fwdSlopeDescends_word_proportion_le (L : ℕ) :
    (((Finset.univ.filter fun w : Fin L → Bool =>
      FwdSlopeDescends L w).card : ℕ) : ℝ) / 2 ^ L ≤ descentChernoffRate ^ L := by
  classical
  calc
    (((Finset.univ.filter fun w : Fin L → Bool =>
        FwdSlopeDescends L w).card : ℕ) : ℝ) / 2 ^ L =
        ∑ w : Fin L → Bool,
          if FwdSlopeDescends L w then 1 / (2 : ℝ) ^ L else 0 := by
            rw [Finset.card_filter]
            push_cast
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro w _
            split_ifs <;> norm_num
    _ ≤ ∑ w : Fin L → Bool, descentChernoffWeight w := by
      apply Finset.sum_le_sum
      intro w _
      split_ifs with hw
      · exact (fwdSlopeDescends_weight_lt w hw).le
      · unfold descentChernoffWeight
        positivity
    _ = _ := sum_descentChernoffWeight L

theorem bwdSlopeDescends_word_proportion_le (L : ℕ) :
    (∑ w : Fin L → Bool,
      if BwdSlopeDescends L w then (2 : ℝ) ^ latticeMarked w else 0) / 3 ^ L ≤
        descentChernoffRate ^ L := by
  classical
  calc
    (∑ w : Fin L → Bool,
        if BwdSlopeDescends L w then (2 : ℝ) ^ latticeMarked w else 0) / 3 ^ L =
        ∑ w : Fin L → Bool,
          if BwdSlopeDescends L w then
            (2 : ℝ) ^ latticeMarked w / 3 ^ L else 0 := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro w _
              split_ifs <;> norm_num
    _ ≤ ∑ w : Fin L → Bool, descentChernoffWeight w := by
      apply Finset.sum_le_sum
      intro w _
      split_ifs with hw
      · exact (bwdSlopeDescends_weight_lt w hw).le
      · unfold descentChernoffWeight
        positivity
    _ = _ := sum_descentChernoffWeight L

/-- At most a `ρ^L` share of forward residues have descending length-`L` affine slope. -/
theorem fwdSlopeDescends_residue_proportion_le (L : ℕ) :
    (Nat.count (fun r : ℕ => FwdSlopeDescends L (amusicalForwardWord L r))
      (4 ^ L) : ℝ) / 4 ^ L ≤ descentChernoffRate ^ L := by
  rw [show Nat.count
      (fun r : ℕ => FwdSlopeDescends L (amusicalForwardWord L (r : ℤ))) (4 ^ L) =
        ∑ w : Fin L → Bool, if FwdSlopeDescends L w then 2 ^ L else 0 from
      count_amusicalForwardWord_pred L (FwdSlopeDescends L)]
  push_cast
  calc
    (∑ w : Fin L → Bool, if FwdSlopeDescends L w then (2 : ℝ) ^ L else 0) /
        (4 : ℝ) ^ L =
      (((Finset.univ.filter fun w : Fin L → Bool => FwdSlopeDescends L w).card : ℕ) : ℝ) /
        2 ^ L := by
          rw [show (4 : ℝ) ^ L = 2 ^ L * 2 ^ L by rw [← mul_pow]; norm_num]
          rw [← Finset.sum_filter]
          simp only [Finset.sum_const, nsmul_eq_mul]
          field_simp
    _ ≤ _ := fwdSlopeDescends_word_proportion_le L

/-- At most a `ρ^L` share of backward residues have descending length-`L` affine slope. -/
theorem bwdSlopeDescends_residue_proportion_le (L : ℕ) :
    (Nat.count (fun r : ℕ => BwdSlopeDescends L (amusicalBackwardWord L r))
      (3 ^ L) : ℝ) / 3 ^ L ≤ descentChernoffRate ^ L := by
  rw [show Nat.count
      (fun r : ℕ => BwdSlopeDescends L (amusicalBackwardWord L (r : ℤ))) (3 ^ L) =
        ∑ w : Fin L → Bool,
          if BwdSlopeDescends L w then 2 ^ latticeMarked w else 0 from
      count_amusicalBackwardWord_pred L (BwdSlopeDescends L)]
  push_cast
  exact bwdSlopeDescends_word_proportion_le L

theorem fwdSlopeDescends_residue_proportion_le_ninetyNineHundredths (L : ℕ) :
    (Nat.count (fun r : ℕ => FwdSlopeDescends L (amusicalForwardWord L r))
      (4 ^ L) : ℝ) / 4 ^ L ≤ ((99 : ℝ) / 100) ^ L := by
  calc
    _ ≤ descentChernoffRate ^ L := fwdSlopeDescends_residue_proportion_le L
    _ ≤ ((99 : ℝ) / 100) ^ L := by
      unfold descentChernoffRate
      gcongr
      exact descentChernoffRate_lt_ninetyNineHundredths.le

theorem bwdSlopeDescends_residue_proportion_le_ninetyNineHundredths (L : ℕ) :
    (Nat.count (fun r : ℕ => BwdSlopeDescends L (amusicalBackwardWord L r))
      (3 ^ L) : ℝ) / 3 ^ L ≤ ((99 : ℝ) / 100) ^ L := by
  calc
    _ ≤ descentChernoffRate ^ L := bwdSlopeDescends_residue_proportion_le L
    _ ≤ ((99 : ℝ) / 100) ^ L := by
      unfold descentChernoffRate
      gcongr
      exact descentChernoffRate_lt_ninetyNineHundredths.le

/-! ## Initial-interval bounds for descent events -/

/-- A periodic predicate whose one-period proportion is at most `q` has at most `q X + M`
members in `[0,X)`.  The additive period is the incomplete final block. -/
theorem count_periodic_le_mul_add_period (P : ℕ → Prop) [DecidablePred P]
    (M : ℕ) (hM : 0 < M) (hP : ∀ n, P n ↔ P (n % M)) (q : ℝ)
    (hq : (Nat.count P M : ℝ) / M ≤ q) (X : ℕ) :
    (Nat.count P X : ℝ) ≤ q * X + M := by
  have hb := (WindowCount.count_periodic_bounds P M hM hP X).2
  have hcount : Nat.count P M ≤ M := Nat.count_le _
  have hdiv : X / M * M ≤ X := Nat.div_mul_le_self X M
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hqnonneg : 0 ≤ q := by
    exact le_trans (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hq
  have hq' : (Nat.count P M : ℝ) ≤ q * M := by
    rwa [div_le_iff₀ hMreal] at hq
  have hbR : (Nat.count P X : ℝ) ≤
      (((X / M : ℕ) : ℝ) + 1) * Nat.count P M := by exact_mod_cast hb
  have hcountR : (Nat.count P M : ℝ) ≤ M := by exact_mod_cast hcount
  have hdivR : (((X / M : ℕ) : ℝ) * M) ≤ X := by exact_mod_cast hdiv
  have hfloor : ((X / M : ℕ) : ℝ) * Nat.count P M ≤ q * X := by
    calc
      ((X / M : ℕ) : ℝ) * Nat.count P M ≤
          ((X / M : ℕ) : ℝ) * (q * M) := by
        gcongr
      _ = q * (((X / M : ℕ) : ℝ) * M) := by ring
      _ ≤ q * X := by
        gcongr
  calc
    (Nat.count P X : ℝ) ≤ (((X / M : ℕ) : ℝ) + 1) * Nat.count P M := hbR
    _ = ((X / M : ℕ) : ℝ) * Nat.count P M + Nat.count P M := by ring
    _ ≤ q * X + M := add_le_add hfloor hcountR

/-- The length-`L` forward descent event is periodic modulo `4^L`. -/
theorem fwdSlopeDescends_periodic (L n : ℕ) :
    FwdSlopeDescends L (amusicalForwardWord L n) ↔
      FwdSlopeDescends L (amusicalForwardWord L ((n % 4 ^ L : ℕ) : ℤ)) := by
  rw [amusicalForwardWord_natCast_mod]

/-- The length-`L` backward descent event is periodic modulo `3^L`. -/
theorem bwdSlopeDescends_periodic (L n : ℕ) :
    BwdSlopeDescends L (amusicalBackwardWord L n) ↔
      BwdSlopeDescends L (amusicalBackwardWord L ((n % 3 ^ L : ℕ) : ℤ)) := by
  rw [amusicalBackwardWord_natCast_mod]

/-- Forward descents at time `L` occupy at most `(99/100)^L X + 4^L` points of `[0,X)`. -/
theorem count_fwdSlopeDescends_le (L X : ℕ) :
    (Nat.count (fun n : ℕ => FwdSlopeDescends L (amusicalForwardWord L n)) X : ℝ) ≤
      ((99 : ℝ) / 100) ^ L * X + (↑(4 ^ L) : ℝ) := by
  have hq : (Nat.count
      (fun n : ℕ => FwdSlopeDescends L (amusicalForwardWord L n)) (4 ^ L) : ℝ) /
      (4 ^ L : ℕ) ≤ ((99 : ℝ) / 100) ^ L := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      fwdSlopeDescends_residue_proportion_le_ninetyNineHundredths L
  have h := count_periodic_le_mul_add_period _ (4 ^ L) (by positivity)
    (fwdSlopeDescends_periodic L) (((99 : ℝ) / 100) ^ L) hq X
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

/-- Backward descents at time `L` occupy at most `(99/100)^L X + 3^L` points of `[0,X)`. -/
theorem count_bwdSlopeDescends_le (L X : ℕ) :
    (Nat.count (fun n : ℕ => BwdSlopeDescends L (amusicalBackwardWord L n)) X : ℝ) ≤
      ((99 : ℝ) / 100) ^ L * X + (↑(3 ^ L) : ℝ) := by
  have hq : (Nat.count
      (fun n : ℕ => BwdSlopeDescends L (amusicalBackwardWord L n)) (3 ^ L) : ℝ) /
      (3 ^ L : ℕ) ≤ ((99 : ℝ) / 100) ^ L := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      bwdSlopeDescends_residue_proportion_le_ninetyNineHundredths L
  have h := count_periodic_le_mul_add_period _ (3 ^ L) (by positivity)
    (bwdSlopeDescends_periodic L) (((99 : ℝ) / 100) ^ L) hq X
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

/-- Actual forward descents obey the same Chernoff bound, apart from the explicit initial range
where the affine comparison need not yet be controlled by its slope. -/
theorem count_iterate_lt_le (L X : ℕ) (hL : 1 ≤ L) :
    (Nat.count (fun n : ℕ => amusical^[L] (n : ℤ) < n) X : ℝ) ≤
      ((99 : ℝ) / 100) ^ L * X + (↑(4 ^ L) : ℝ) + 2 * 324 ^ L := by
  let P : ℕ → Prop := fun n => amusical^[L] (n : ℤ) < n
  let Q : ℕ → Prop := fun n => FwdSlopeDescends L (amusicalForwardWord L n)
  have heq : ∀ n : ℕ, 2 * 324 ^ L ≤ n → (P n ↔ Q n) := by
    intro n hn
    exact iterate_lt_iff_fwdSlopeDescends_of_ge L n hL hn
  have hc := (count_eventually_congr_bound P Q heq X).1
  have hq := count_fwdSlopeDescends_le L X
  change (Nat.count P X : ℝ) ≤ _
  have hcR : (Nat.count P X : ℝ) ≤ Nat.count Q X + 2 * 324 ^ L := by
    exact_mod_cast hc
  linarith

/-- Actual backward descents obey the same Chernoff bound, apart from the explicit initial range
where the affine comparison need not yet be controlled by its slope. -/
theorem count_inv_iterate_lt_le (L X : ℕ) (hL : 1 ≤ L) :
    (Nat.count (fun n : ℕ => amusicalInv^[L] (n : ℤ) < n) X : ℝ) ≤
      ((99 : ℝ) / 100) ^ L * X + (↑(3 ^ L) : ℝ) + 2 * 324 ^ L := by
  let P : ℕ → Prop := fun n => amusicalInv^[L] (n : ℤ) < n
  let Q : ℕ → Prop := fun n => BwdSlopeDescends L (amusicalBackwardWord L n)
  have heq : ∀ n : ℕ, 2 * 324 ^ L ≤ n → (P n ↔ Q n) := by
    intro n hn
    exact inv_iterate_lt_iff_bwdSlopeDescends_of_ge L n hL hn
  have hc := (count_eventually_congr_bound P Q heq X).1
  have hq := count_bwdSlopeDescends_le L X
  change (Nat.count P X : ℝ) ≤ _
  have hcR : (Nat.count P X : ℝ) ≤ Nat.count Q X + 2 * 324 ^ L := by
    exact_mod_cast hc
  linarith

/-- A finite union of events in an initial interval has size at most the sum of their sizes. -/
theorem count_exists_mem_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : ι → ℕ → Prop) [∀ i, DecidablePred (P i)] (X : ℕ) :
    Nat.count (fun n => ∃ i : ↥s, P i n) X ≤ ∑ i ∈ s, Nat.count (P i) X := by
  classical
  rw [Nat.count_eq_card_filter_range]
  let A : ι → Finset ℕ := fun i => (Finset.range X).filter (P i)
  have hsub : (Finset.range X).filter (fun n => ∃ i : ↥s, P i n) ⊆ s.biUnion A := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    rcases hn.2 with ⟨i, hPin⟩
    exact Finset.mem_biUnion.mpr
      ⟨i, i.property, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn.1, hPin⟩⟩
  calc
    ((Finset.range X).filter (fun n => ∃ i : ↥s, P i n)).card ≤ (s.biUnion A).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i ∈ s, (A i).card := Finset.card_biUnion_le
    _ = ∑ i ∈ s, Nat.count (P i) X := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Nat.count_eq_card_filter_range (p := P i) (n := X)).symm

/-- Union bound for a forward or backward descent at some time `K < i ≤ L`. -/
theorem count_descent_between_le (K L X : ℕ) :
    (Nat.count (fun n : ℕ => ∃ i : ↥(Finset.Icc (K + 1) L),
      (amusical^[i] (n : ℤ) < n ∨ amusicalInv^[i] (n : ℤ) < n)) X : ℝ) ≤
      ∑ i ∈ Finset.Icc (K + 1) L,
        (2 * ((99 : ℝ) / 100) ^ i * X + 4 ^ i + 3 ^ i + 4 * 324 ^ i) := by
  let P : ℕ → ℕ → Prop := fun i n =>
    amusical^[i] (n : ℤ) < n ∨ amusicalInv^[i] (n : ℤ) < n
  have hu := count_exists_mem_le_sum (Finset.Icc (K + 1) L) P X
  have huR : (Nat.count (fun n : ℕ => ∃ i : ↥(Finset.Icc (K + 1) L), P i n) X : ℝ) ≤
      ∑ i ∈ Finset.Icc (K + 1) L, (Nat.count (P i) X : ℝ) := by
    exact_mod_cast hu
  refine huR.trans (Finset.sum_le_sum fun i hi => ?_)
  have hi1 : 1 ≤ i := by
    have := (Finset.mem_Icc.mp hi).1
    omega
  have hf := count_iterate_lt_le i X hi1
  have hb := count_inv_iterate_lt_le i X hi1
  have hor := count_exists_mem_le_sum ({true, false} : Finset Bool)
    (fun b n => if b then amusical^[i] (n : ℤ) < n else amusicalInv^[i] (n : ℤ) < n) X
  have hor' : Nat.count (P i) X ≤
      Nat.count (fun n : ℕ => amusical^[i] (n : ℤ) < n) X +
        Nat.count (fun n : ℕ => amusicalInv^[i] (n : ℤ) < n) X := by
    simpa [P, or_comm, add_comm] using hor
  have horR : (Nat.count (P i) X : ℝ) ≤
      Nat.count (fun n : ℕ => amusical^[i] (n : ℤ) < n) X +
        Nat.count (fun n : ℕ => amusicalInv^[i] (n : ℤ) < n) X := by
    exact_mod_cast hor'
  norm_num [Nat.cast_add, Nat.cast_pow] at hf hb ⊢
  linarith

/-- The geometric part of the finite descent union is uniformly bounded by its infinite tail. -/
theorem sum_ninetyNineHundredths_Icc_le (K L : ℕ) :
    ∑ i ∈ Finset.Icc (K + 1) L, ((99 : ℝ) / 100) ^ i ≤
      100 * ((99 : ℝ) / 100) ^ (K + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  calc
    ∑ i ∈ Finset.Ico (K + 1) (L + 1), ((99 : ℝ) / 100) ^ i ≤
        ((99 : ℝ) / 100) ^ (K + 1) / (1 - (99 : ℝ) / 100) :=
      geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ = 100 * ((99 : ℝ) / 100) ^ (K + 1) := by ring

/-- A coarse bound for the incomplete-period errors in the finite descent union. -/
theorem sum_descent_period_errors_le (K L : ℕ) :
    ∑ i ∈ Finset.Icc (K + 1) L,
        ((4 : ℝ) ^ i + 3 ^ i + 4 * 324 ^ i) ≤ 6 * (L + 1) * 324 ^ L := by
  calc
    ∑ i ∈ Finset.Icc (K + 1) L,
        ((4 : ℝ) ^ i + 3 ^ i + 4 * 324 ^ i) ≤
        ∑ _i ∈ Finset.Icc (K + 1) L, 6 * 324 ^ L := by
      apply Finset.sum_le_sum
      intro i hi
      have hiL : i ≤ L := (Finset.mem_Icc.mp hi).2
      have h4 : (4 : ℝ) ^ i ≤ 324 ^ i := by gcongr <;> norm_num
      have h3 : (3 : ℝ) ^ i ≤ 324 ^ i := by gcongr <;> norm_num
      have hpow : (324 : ℝ) ^ i ≤ 324 ^ L := by
        exact pow_le_pow_right₀ (by norm_num) hiL
      nlinarith [show (0 : ℝ) ≤ 324 ^ i by positivity]
    _ ≤ 6 * (L + 1) * 324 ^ L := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.Icc (K + 1) L).card ≤ L + 1 := by
        rw [Nat.card_Icc]
        omega
      have hcardR : ((Finset.Icc (K + 1) L).card : ℝ) ≤ L + 1 := by exact_mod_cast hcard
      nlinarith [mul_le_mul_of_nonneg_right hcardR
        (show (0 : ℝ) ≤ 6 * 324 ^ L by positivity)]

/-- The finite descent union has a geometric main term and an explicit sublinear-scale error. -/
theorem count_descent_between_geometric_le (K L X : ℕ) :
    (Nat.count (fun n : ℕ => ∃ i : ↥(Finset.Icc (K + 1) L),
      (amusical^[i] (n : ℤ) < n ∨ amusicalInv^[i] (n : ℤ) < n)) X : ℝ) ≤
      200 * ((99 : ℝ) / 100) ^ (K + 1) * X + 6 * (L + 1) * 324 ^ L := by
  refine (count_descent_between_le K L X).trans ?_
  have hmain := sum_ninetyNineHundredths_Icc_le K L
  have herr := sum_descent_period_errors_le K L
  have hsplit :
      (∑ i ∈ Finset.Icc (K + 1) L,
        (2 * ((99 : ℝ) / 100) ^ i * X + 4 ^ i + 3 ^ i + 4 * 324 ^ i)) =
        (∑ i ∈ Finset.Icc (K + 1) L, 2 * ((99 : ℝ) / 100) ^ i * X) +
          ∑ i ∈ Finset.Icc (K + 1) L, (4 ^ i + 3 ^ i + 4 * 324 ^ i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsplit]
  calc
    ∑ i ∈ Finset.Icc (K + 1) L, 2 * ((99 : ℝ) / 100) ^ i * X +
          ∑ i ∈ Finset.Icc (K + 1) L, (4 ^ i + 3 ^ i + 4 * 324 ^ i) =
        2 * X * (∑ i ∈ Finset.Icc (K + 1) L, ((99 : ℝ) / 100) ^ i) +
          ∑ i ∈ Finset.Icc (K + 1) L, (4 ^ i + 3 ^ i + 4 * 324 ^ i) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ 2 * X * (100 * ((99 : ℝ) / 100) ^ (K + 1)) +
          6 * (L + 1) * 324 ^ L := by gcongr
    _ = 200 * ((99 : ℝ) / 100) ^ (K + 1) * X + 6 * (L + 1) * 324 ^ L := by
      ring

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

/-- On an infinite orbit, a centered-window minimum outside the central `K` offsets forces a
strict descent at some forward or backward time between `K+1` and `L`.  This reduces the
exceptional-offset event in Lemma T to the union of one-sided descent events. -/
theorem centered_minimizer_outside_implies_descent {L K : ℕ} {n t : ℤ}
    (hinf : (amusicalOrbit n).Infinite) (ht : |t| ≤ L) (hout : K < |t|)
    (hmin : ∀ s : ℤ, |s| ≤ L →
      (amusicalPerm ^ t) n ≤ (amusicalPerm ^ s) n) :
    (∃ i : ℕ, K < i ∧ i ≤ L ∧ amusical^[i] n < n) ∨
      ∃ i : ℕ, K < i ∧ i ≤ L ∧ amusicalInv^[i] n < n := by
  have hinj := perm_zpow_apply_injective_of_infinite amusicalPerm hinf
  have hle : (amusicalPerm ^ t) n ≤ n := by simpa using hmin 0 (by simp)
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    simp only [abs_zero] at hout
    omega
  rcases lt_or_gt_of_ne ht0 with htneg | htpos
  · right
    rw [abs_of_neg htneg] at hout ht
    refine ⟨(-t).natAbs, ?_, ?_, ?_⟩
    · have hi : ((-t).natAbs : ℤ) = -t := by simp [abs_of_neg htneg]
      exact_mod_cast (show (K : ℤ) < ((-t).natAbs : ℤ) by rw [hi]; exact hout)
    · have hi : ((-t).natAbs : ℤ) = -t := by simp [abs_of_neg htneg]
      exact_mod_cast (show ((-t).natAbs : ℤ) ≤ L by rw [hi]; exact ht)
    · rw [amusicalInv_iterate_eq_perm_pow]
      have hpow : (-((-t).natAbs : ℤ)) = t := by simp [abs_of_neg htneg]
      rw [hpow]
      exact lt_of_le_of_ne hle fun heq => by
        apply ht0
        exact hinj (by simpa using heq)
  · left
    rw [abs_of_pos htpos] at hout ht
    refine ⟨t.natAbs, ?_, ?_, ?_⟩
    · have hi : (t.natAbs : ℤ) = t := by simp [abs_of_pos htpos]
      exact_mod_cast (show (K : ℤ) < (t.natAbs : ℤ) by rw [hi]; exact hout)
    · have hi : (t.natAbs : ℤ) = t := by simp [abs_of_pos htpos]
      exact_mod_cast (show (t.natAbs : ℤ) ≤ L by rw [hi]; exact ht)
    · rw [amusical_iterate_eq_perm_pow]
      have hpow : (t.natAbs : ℤ) = t := by simp [abs_of_pos htpos]
      rw [hpow]
      exact lt_of_le_of_ne hle fun heq => by
        apply ht0
        exact hinj (by simpa using heq)

end CollatzMoonshot.Amusical
