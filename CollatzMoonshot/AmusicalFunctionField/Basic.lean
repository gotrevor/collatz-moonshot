/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar

/-!
# Helpers for the `𝔽₂[t]` twin

`fQ` and `fU` are verbatim copies of `twinQ` and `twinU` (the main file proves the two equal by
`rfl`), so these helpers can sit below `CollatzMoonshot.AmusicalFunctionField` in the import graph.

* Branch lemmas `fU_E`, `fU_A`, `fU_B`, `fU_C` and the four-way decomposition `fU_cases`.
* Bijectivity (`fU_bijective`): images `Q k + s` with `deg s < 2` are unique by division with
  remainder.
* Theorem F (`fU_minimalPeriod`): the `E` phase is multiplication by `Q / t`; the `B` phase runs
  through `P k = e_B (u^{m−3} Q^m + t^{3(m−k)} G k)` with `u = t + 1`, `G (k+1) = Q G k + t^{3k}`,
  and every `B` step is the single identity `t³ P (k+1) = Q P k + e_B` (Frobenius:
  `(u Q)^m = (t³ + 1)^m = t^{3m} + 1`).
-/

namespace CollatzMoonshot.Amusical.FFTwin

open Polynomial

/-- Verbatim copy of `twinQ`. -/
noncomputable def fQ : (ZMod 2)[X] := X ^ 2 + X + 1

/-- Verbatim copy of `twinU`. -/
noncomputable def fU (n : (ZMod 2)[X]) : (ZMod 2)[X] :=
  if n.coeff 0 = 0 then fQ * (n /ₘ X)
  else if n.coeff 1 = 0 then fQ * ((n - 1) /ₘ X ^ 2) + 1
  else if n.coeff 2 = 0 then fQ * ((n - 1 - X) /ₘ X ^ 3) + X
  else fQ * ((n - 1 - X - X ^ 2) /ₘ X ^ 3) + (1 + X)

lemma fQ_monic : fQ.Monic := by unfold fQ; monicity!

lemma fQ_degree : fQ.degree = 2 := by unfold fQ; compute_degree!

lemma fQ_ne_zero : fQ ≠ 0 := fQ_monic.ne_zero

/-! ## The four branches -/

lemma fU_E (k : (ZMod 2)[X]) : fU (X * k) = fQ * k := by
  have h0 : (X * k).coeff 0 = 0 := by simp
  rw [fU, if_pos h0, mul_divByMonic_cancel_left k monic_X]

lemma fU_A (k : (ZMod 2)[X]) : fU (1 + X ^ 2 * k) = fQ * k + 1 := by
  have h0 : (1 + X ^ 2 * k).coeff 0 ≠ 0 := by
    simp [coeff_add, coeff_one]
  have h1 : (1 + X ^ 2 * k).coeff 1 = 0 := by
    simp [coeff_add, coeff_one, coeff_X_pow_mul']
  rw [fU, if_neg h0, if_pos h1, add_sub_cancel_left,
    mul_divByMonic_cancel_left k (monic_X_pow 2)]

lemma fU_B (k : (ZMod 2)[X]) : fU (1 + X + X ^ 3 * k) = fQ * k + X := by
  have h0 : (1 + X + X ^ 3 * k).coeff 0 ≠ 0 := by
    simp [coeff_add, coeff_one, coeff_X]
  have h1 : (1 + X + X ^ 3 * k).coeff 1 ≠ 0 := by
    simp [coeff_add, coeff_one, coeff_X, coeff_X_pow_mul']
  have h2 : (1 + X + X ^ 3 * k).coeff 2 = 0 := by
    simp [coeff_add, coeff_one, coeff_X, coeff_X_pow_mul']
  have hs : (1 + X + X ^ 3 * k : (ZMod 2)[X]) - 1 - X = X ^ 3 * k := by ring
  rw [fU, if_neg h0, if_neg h1, if_pos h2, hs, mul_divByMonic_cancel_left k (monic_X_pow 3)]

lemma fU_C (k : (ZMod 2)[X]) : fU (1 + X + X ^ 2 + X ^ 3 * k) = fQ * k + (1 + X) := by
  have h0 : (1 + X + X ^ 2 + X ^ 3 * k).coeff 0 ≠ 0 := by
    simp [coeff_add, coeff_one, coeff_X, coeff_X_pow]
  have h1 : (1 + X + X ^ 2 + X ^ 3 * k).coeff 1 ≠ 0 := by
    simp [coeff_add, coeff_one, coeff_X, coeff_X_pow, coeff_X_pow_mul']
  have h2 : (1 + X + X ^ 2 + X ^ 3 * k).coeff 2 ≠ 0 := by
    simp [coeff_add, coeff_one, coeff_X, coeff_X_pow, coeff_X_pow_mul']
  have hs : (1 + X + X ^ 2 + X ^ 3 * k : (ZMod 2)[X]) - 1 - X - X ^ 2 = X ^ 3 * k := by ring
  rw [fU, if_neg h0, if_neg h1, if_neg h2, hs, mul_divByMonic_cancel_left k (monic_X_pow 3)]

lemma zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  exacts [Or.inl rfl, Or.inr rfl]

/-- Every polynomial lies in exactly one branch domain (existence half). -/
lemma fU_cases (n : (ZMod 2)[X]) :
    (∃ k, n = X * k) ∨ (∃ k, n = 1 + X ^ 2 * k) ∨ (∃ k, n = 1 + X + X ^ 3 * k) ∨
      (∃ k, n = 1 + X + X ^ 2 + X ^ 3 * k) := by
  rcases zmod2_cases (n.coeff 0) with h0 | h0
  · left
    exact X_dvd_iff.mpr h0
  right
  rcases zmod2_cases (n.coeff 1) with h1 | h1
  · left
    obtain ⟨k, hk⟩ : X ^ 2 ∣ n - 1 := by
      rw [X_pow_dvd_iff]
      intro d hd
      interval_cases d <;> simp [coeff_one, h0, h1]
    exact ⟨k, by rw [← hk]; ring⟩
  right
  rcases zmod2_cases (n.coeff 2) with h2 | h2
  · left
    obtain ⟨k, hk⟩ : X ^ 3 ∣ n - 1 - X := by
      rw [X_pow_dvd_iff]
      intro d hd
      interval_cases d <;> simp [coeff_one, coeff_X, h0, h1, h2]
    exact ⟨k, by rw [← hk]; ring⟩
  · right
    obtain ⟨k, hk⟩ : X ^ 3 ∣ n - 1 - X - X ^ 2 := by
      rw [X_pow_dvd_iff]
      intro d hd
      interval_cases d <;> simp [coeff_one, coeff_X, coeff_X_pow, h0, h1, h2]
    exact ⟨k, by rw [← hk]; ring⟩

/-! ## Bijectivity -/

lemma quot_rem_unique {k k' s s' : (ZMod 2)[X]} (hs : s.degree < 2) (hs' : s'.degree < 2)
    (h : fQ * k + s = fQ * k' + s') : k = k' ∧ s = s' := by
  have h1 := div_modByMonic_unique k s fQ_monic ⟨by rw [add_comm], by rwa [fQ_degree]⟩
  have h2 := div_modByMonic_unique k' s' fQ_monic ⟨by rw [add_comm, ← h], by rwa [fQ_degree]⟩
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

lemma deg_zero : (0 : (ZMod 2)[X]).degree < 2 := by
  rw [degree_zero]; exact WithBot.bot_lt_coe 2
lemma deg_one : (1 : (ZMod 2)[X]).degree < 2 := by
  rw [degree_one]; exact compareOfLessAndEq_eq_lt.mp rfl
lemma deg_X : (X : (ZMod 2)[X]).degree < 2 := by
  rw [degree_X]; exact compareOfLessAndEq_eq_lt.mp rfl
lemma deg_one_add_X : (1 + X : (ZMod 2)[X]).degree < 2 := by
  have : (1 + X : (ZMod 2)[X]).degree ≤ 1 := by compute_degree!
  exact this.trans_lt (compareOfLessAndEq_eq_lt.mp rfl)

lemma fU_surjective : Function.Surjective fU := by
  intro y
  set r := y %ₘ fQ with hr
  have hy : fQ * (y /ₘ fQ) + r = y := by rw [add_comm]; exact modByMonic_add_div y fQ
  have hdeg : r.degree < 2 := by rw [← fQ_degree]; exact degree_modByMonic_lt y fQ_monic
  have hnat : r.natDegree ≤ 1 := by
    rcases eq_or_ne r 0 with h | h
    · simp [h]
    · have := (natDegree_lt_iff_degree_lt (n := 2) h).2 hdeg
      omega
  have hlin := eq_X_add_C_of_natDegree_le_one hnat
  set q := y /ₘ fQ
  rcases zmod2_cases (r.coeff 0) with a | a <;> rcases zmod2_cases (r.coeff 1) with b | b <;>
    rw [a, b] at hlin <;> simp only [map_zero, map_one, zero_mul, one_mul, add_zero,
      zero_add] at hlin
  · exact ⟨X * q, by rw [fU_E, ← hy, hlin, add_zero]⟩
  · exact ⟨1 + X + X ^ 3 * q, by rw [fU_B, ← hy, hlin]⟩
  · exact ⟨1 + X ^ 2 * q, by rw [fU_A, ← hy, hlin]⟩
  · exact ⟨1 + X + X ^ 2 + X ^ 3 * q, by rw [fU_C, ← hy, hlin, add_comm X 1]⟩

/-- The image of `n` together with its branch: `fU n = Q k + s`, and `n` is the branch preimage. -/
lemma fU_injective : Function.Injective fU := by
  intro a b hab
  have c0 : (0 : (ZMod 2)[X]) ≠ 1 := zero_ne_one
  have c1 : (0 : (ZMod 2)[X]) ≠ X := fun h => by
    simpa using congrArg (coeff · 1) h
  have c2 : (0 : (ZMod 2)[X]) ≠ 1 + X := fun h => by
    simpa using congrArg (coeff · 0) h
  have c3 : (1 : (ZMod 2)[X]) ≠ X := fun h => by
    simpa using congrArg (coeff · 0) h
  have c4 : (1 : (ZMod 2)[X]) ≠ 1 + X := fun h => by
    simpa using congrArg (coeff · 1) h
  have c5 : (X : (ZMod 2)[X]) ≠ 1 + X := fun h => by
    simpa using congrArg (coeff · 0) h
  rcases fU_cases a with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ <;>
  rcases fU_cases b with ⟨k', rfl⟩ | ⟨k', rfl⟩ | ⟨k', rfl⟩ | ⟨k', rfl⟩ <;>
  simp only [fU_E, fU_A, fU_B, fU_C] at hab
  · have := quot_rem_unique deg_zero deg_zero (by simpa using hab); rw [this.1]
  · exact absurd (quot_rem_unique deg_zero deg_one (by simpa using hab)).2 c0
  · exact absurd (quot_rem_unique deg_zero deg_X (by simpa using hab)).2 c1
  · exact absurd (quot_rem_unique deg_zero deg_one_add_X (by simpa using hab)).2 c2
  · exact absurd (quot_rem_unique deg_one deg_zero (by simpa using hab)).2.symm c0
  · rw [(quot_rem_unique deg_one deg_one hab).1]
  · exact absurd (quot_rem_unique deg_one deg_X hab).2 c3
  · exact absurd (quot_rem_unique deg_one deg_one_add_X hab).2 c4
  · exact absurd (quot_rem_unique deg_X deg_zero (by simpa using hab)).2.symm c1
  · exact absurd (quot_rem_unique deg_X deg_one hab).2.symm c3
  · rw [(quot_rem_unique deg_X deg_X hab).1]
  · exact absurd (quot_rem_unique deg_X deg_one_add_X hab).2 c5
  · exact absurd (quot_rem_unique deg_one_add_X deg_zero (by simpa using hab)).2.symm c2
  · exact absurd (quot_rem_unique deg_one_add_X deg_one hab).2.symm c4
  · exact absurd (quot_rem_unique deg_one_add_X deg_X hab).2.symm c5
  · rw [(quot_rem_unique deg_one_add_X deg_one_add_X hab).1]

theorem fU_bijective : Function.Bijective fU := ⟨fU_injective, fU_surjective⟩

end CollatzMoonshot.Amusical.FFTwin
