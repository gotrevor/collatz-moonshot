/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalLateDrops
import CollatzMoonshot.AmusicalDecouple.Density

/-!
# The forward and backward windows are eventually periodic

Helpers for Corollary MD in `CollatzMoonshot/AmusicalDecouple.lean`.  Above the height
`4^L 3^L (windowBound L + 1)`, surviving the forward `L`-window is a property of the branch word,
which depends only on `n mod 4^L`; likewise backward, mod `3^L`.  `isWin_iff_good_of_large` is a
copy of the private `windowSurvivors_iff_good_of_large` of `AmusicalGlobal.lean`, restated for
`IsFwdWin` / `IsBwdWin`.
-/

namespace CollatzMoonshot.Amusical.Decouple

/-- Above the joint window threshold, each one-sided semantic condition is independently
equivalent to its branch-word condition. -/
theorem isWin_iff_good_of_large (L n : ℕ)
    (hn : 4 ^ L * 3 ^ L * (windowBound L + 1) ≤ n) :
    (IsFwdWin L n ↔ FwdGood L (amusicalForwardWord L n)) ∧
      (IsBwdWin L n ↔ BwdGood L (amusicalBackwardWord L n)) := by
  set M := 4 ^ L * 3 ^ L with hM
  have hMpos : 0 < M := by positivity
  set c := n % M with hc
  set q := n / M with hq
  have hcM : c < M := Nat.mod_lt _ hMpos
  have hqge : windowBound L + 1 ≤ q :=
    (Nat.le_div_iff_mul_le hMpos).mpr (by linarith)
  have hnq : (n : ℤ) = c + M * q := by
    have h := Nat.mod_add_div n M
    exact_mod_cast h.symm
  have hnF : (n : ℤ) = c + 4 ^ L * (3 ^ L * q) := by
    rw [hnq, hM]
    push_cast
    ring
  have hnB : (n : ℤ) = c + 3 ^ L * (4 ^ L * q) := by
    rw [hnq, hM]
    push_cast
    ring
  have hpatF : amusicalForwardWord L n = amusicalForwardWord L c := by
    rw [hnF, amusicalForwardWord_add_pow_four_mul]
  have hpatB : amusicalBackwardWord L n = amusicalBackwardWord L c := by
    rw [hnB, amusicalBackwardWord_add_pow_three_mul]
  rw [hpatF, hpatB]
  have hbound : ∀ t, t ≤ L → |amusical^[t] (c : ℤ) - c| < q ∧
      |amusicalInv^[t] (c : ℤ) - c| < q := by
    intro t ht
    have h1 : (amusical^[t] (c : ℤ) - c).natAbs +
        (amusicalInv^[t] (c : ℤ) - c).natAbs ≤ windowBound L := by
      unfold windowBound
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr hcM))
      exact Finset.single_le_sum
        (f := fun t => (amusical^[t] (c : ℤ) - c).natAbs +
          (amusicalInv^[t] (c : ℤ) - c).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have h2 : ((amusical^[t] (c : ℤ) - c).natAbs : ℤ) +
        ((amusicalInv^[t] (c : ℤ) - c).natAbs : ℤ) ≤ windowBound L := by
      exact_mod_cast h1
    have h3 : (windowBound L : ℤ) + 1 ≤ q := by exact_mod_cast hqge
    rw [Int.natCast_natAbs, Int.natCast_natAbs] at h2
    have hf := abs_nonneg (amusical^[t] (c : ℤ) - c)
    have hb := abs_nonneg (amusicalInv^[t] (c : ℤ) - c)
    constructor <;> linarith
  have hq3 : (q : ℤ) ≤ 3 ^ L * q :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hq4 : (q : ℤ) ≤ 4 ^ L * q :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hF : ∀ t, 1 ≤ t → t ≤ L → ((n : ℤ) ≤ amusical^[t] n ↔
      2 ^ (t + ((Finset.univ.filter fun i : Fin L =>
        i.val < t ∧ amusicalForwardWord L c i = true).card)) < 3 ^ t) := by
    intro t ht1 ht
    rw [hnF, amusical_iterate_add_pow_four_mul_slope L t ht]
    rw [show (4 : ℤ) ^ (L - t) * 3 ^ t * 2 ^ amusicalForwardEvenCount t c *
        (3 ^ L * q) =
      (4 ^ (L - t) * 3 ^ t * 2 ^ amusicalForwardEvenCount t c) *
        (3 ^ L * q) by ring]
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
  constructor
  · constructor
    · intro hf t ht1 ht
      exact (hF t ht1 ht).mp (hf t ht1 ht)
    · intro hf t ht1 ht
      exact (hF t ht1 ht).mpr (hf t ht1 ht)
  · constructor
    · intro hb t ht1 ht
      exact (hB t ht1 ht).mp (hb t ht1 ht)
    · intro hb t ht1 ht
      exact (hB t ht1 ht).mpr (hb t ht1 ht)

/-- **The forward `L`-window is eventually `2^(2L)`-periodic.** -/
theorem evPer_fwdWin (L : ℕ) :
    EvPer {n : ℕ | IsFwdWin L (n : ℤ)} (2 ^ (2 * L)) (4 ^ L * 3 ^ L * (windowBound L + 1)) := by
  intro n hn
  have h4 : (2 : ℕ) ^ (2 * L) = 4 ^ L := by rw [pow_mul]; norm_num
  have hn' : 4 ^ L * 3 ^ L * (windowBound L + 1) ≤ n + 2 ^ (2 * L) :=
    Nat.le_add_right_of_le hn
  simp only [Set.mem_ofPred_eq]
  rw [(isWin_iff_good_of_large L n hn).1, (isWin_iff_good_of_large L _ hn').1,
    amusicalForwardWord_natCast_mod L n, amusicalForwardWord_natCast_mod L (n + 2 ^ (2 * L)),
    h4, Nat.add_mod_right]

/-- **The backward `L`-window is eventually `3^L`-periodic.** -/
theorem evPer_bwdWin (L : ℕ) :
    EvPer {n : ℕ | IsBwdWin L (n : ℤ)} (3 ^ L) (4 ^ L * 3 ^ L * (windowBound L + 1)) := by
  intro n hn
  have hn' : 4 ^ L * 3 ^ L * (windowBound L + 1) ≤ n + 3 ^ L :=
    Nat.le_add_right_of_le hn
  simp only [Set.mem_ofPred_eq]
  rw [(isWin_iff_good_of_large L n hn).2, (isWin_iff_good_of_large L _ hn').2,
    amusicalBackwardWord_natCast_mod L n, amusicalBackwardWord_natCast_mod L (n + 3 ^ L),
    Nat.add_mod_right]

end CollatzMoonshot.Amusical.Decouple
