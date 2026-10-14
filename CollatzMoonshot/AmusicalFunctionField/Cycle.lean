/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalFunctionField.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.ZMod

/-!
# Theorem F for the `𝔽₂[t]` twin, in closed form

Write `m = 2^n` (`n ≥ 2`), `u = t + 1`, `e_B = t⁴ + t³ + 1`, `x₀ = e_B t^m u^{m−3}`.

* `E` phase (`fU_iterate_E`): `x₀ = t^m · c` and each `E` step trades a `t` for a `Q`, so
  `U^m x₀ = Q^m e_B u^{m−3} = P 0`.
* `B` phase: `P k = e_B (u^{m−3} Q^m + t^{3(m−k)} G k)` with `G 0 = 0`, `G (k+1) = Q G k + t^{3k}`.
  A polynomial `P` with `t³ P' = Q P + e_B` is forced into the `B` branch and `U P = P'`
  (`fU_of_step`; this is the affine `B` map with fixed point `e_B / u³`).  The step identity holds
  for `P k` by Frobenius, `u^m Q^m = (t³ + 1)^m = t^{3m} + 1` (`P_step`).
* Closing (`P_last`): `u³ G k = Q^k + t^{3k}`, so `u³ P m = e_B (1 + Q^m) = e_B (t u)^m = u³ x₀`.
* Exactness: the period divides `2m = 2^(n+1)`, and `U^m x₀ = P 0` has constant term `1` while
  `x₀` has constant term `0`.
-/

namespace CollatzMoonshot.Amusical.FFTwin

open Polynomial Function

/-- The `B`-branch numerator `t⁴ + t³ + 1`. -/
noncomputable def eB : (ZMod 2)[X] := X ^ 4 + X ^ 3 + 1

/-- A point satisfying the `B` step identity is in the `B` branch, and `U` is that step. -/
lemma fU_of_step {P P' : (ZMod 2)[X]} (h : X ^ 3 * P' = fQ * P + eB) : fU P = P' := by
  unfold fQ eB at h
  have hP : P = 1 + X + X ^ 3 * (1 + X ^ 2 + (1 + X) * P' + P) := by
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) (-(1 + X)) * h
  rw [hP, fU_B]
  unfold fQ
  linear_combination (norm := (ring_nf <;> reduce_mod_char)) (-1 : (ZMod 2)[X]) * h

/-- The `E` phase: `U^j (t^(j+s) c) = Q^j t^s c`. -/
lemma fU_iterate_E (j s : ℕ) (c : (ZMod 2)[X]) :
    fU^[j] (X ^ (j + s) * c) = fQ ^ j * X ^ s * c := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
    rw [iterate_succ_apply, show X ^ (j + 1 + s) * c = X * (X ^ (j + s) * c) by ring, fU_E,
      show fQ * (X ^ (j + s) * c) = X ^ (j + s) * (fQ * c) by ring, ih]
    ring

/-- The geometric sum `G k = Σ_{i<k} Q^i t^{3(k−1−i)}`, recursively. -/
noncomputable def G : ℕ → (ZMod 2)[X]
  | 0 => 0
  | k + 1 => fQ * G k + X ^ (3 * k)

lemma G_mul (k : ℕ) : (X + 1) ^ 3 * G k = fQ ^ k + X ^ (3 * k) := by
  induction k with
  | zero => simpa [G] using (CharTwo.add_self_eq_zero (1 : (ZMod 2)[X])).symm
  | succ k ih =>
    simp only [G]
    rw [show 3 * (k + 1) = 3 * k + 3 by ring, pow_add]
    unfold fQ at ih ⊢
    linear_combination (norm := (ring_nf <;> reduce_mod_char)) (X ^ 2 + X + 1) * ih

/-- The `B`-phase points. -/
noncomputable def P (m k : ℕ) : (ZMod 2)[X] :=
  eB * ((X + 1) ^ (m - 3) * fQ ^ m + X ^ (3 * (m - k)) * G k)

/-- Frobenius: `u^m Q^m = t^{3m} + 1` for `m = 2^n`. -/
lemma frob_uQ (n : ℕ) : (X + 1 : (ZMod 2)[X]) ^ 2 ^ n * fQ ^ 2 ^ n = X ^ (3 * 2 ^ n) + 1 := by
  have h : (X + 1 : (ZMod 2)[X]) * fQ = X ^ 3 + 1 := by
    unfold fQ
    linear_combination (norm := (ring_nf; reduce_mod_char))
  rw [← mul_pow, h, add_pow_char_pow (p := 2), one_pow, ← pow_mul]

/-- Frobenius: `(t u)^m = 1 + Q^m` for `m = 2^n`. -/
lemma frob_tu (n : ℕ) : (X * (X + 1) : (ZMod 2)[X]) ^ 2 ^ n = 1 + fQ ^ 2 ^ n := by
  have h : (X * (X + 1) : (ZMod 2)[X]) = 1 + fQ := by
    unfold fQ
    linear_combination (norm := (ring_nf; reduce_mod_char))
  rw [h, add_pow_char_pow (p := 2), one_pow]

lemma P_step (n k : ℕ) (hn : 2 ≤ n) (hk : k < 2 ^ n) :
    X ^ 3 * P (2 ^ n) (k + 1) = fQ * P (2 ^ n) k + eB := by
  have hm : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hF := frob_uQ n
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ n = k + 1 + t := ⟨2 ^ n - (k + 1), by omega⟩
  rw [ht] at hF ⊢
  have e1 : k + 1 + t - (k + 1) = t := by omega
  have e2 : k + 1 + t - k = t + 1 := by omega
  have hV : (X + 1 : (ZMod 2)[X]) ^ (k + 1 + t) = (X + 1) ^ 3 * (X + 1) ^ (k + 1 + t - 3) := by
    rw [← pow_add]; congr 1; omega
  rw [hV, show (X : (ZMod 2)[X]) ^ (3 * (k + 1 + t)) = X ^ 3 * X ^ (3 * k) * X ^ (3 * t) by
    rw [← pow_add, ← pow_add]; congr 1; ring] at hF
  simp only [P, G, e1, e2]
  rw [show (X : (ZMod 2)[X]) ^ (3 * (t + 1)) = X ^ (3 * t) * X ^ 3 by
    rw [← pow_add]; ring_nf]
  generalize fQ ^ (k + 1 + t) = W at hF ⊢
  generalize (X + 1 : (ZMod 2)[X]) ^ (k + 1 + t - 3) = V at hF ⊢
  generalize (X : (ZMod 2)[X]) ^ (3 * k) = Z at hF ⊢
  generalize (X : (ZMod 2)[X]) ^ (3 * t) = Y at hF ⊢
  generalize G k = g
  unfold fQ eB
  linear_combination (norm := (ring_nf; reduce_mod_char)) (X ^ 4 + X ^ 3 + 1) * hF

lemma P_iterate (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ 2 ^ n) :
    fU^[k] (P (2 ^ n) 0) = P (2 ^ n) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih (by omega)]
    exact fU_of_step (P_step n k hn (by omega))

lemma P_last (n : ℕ) (hn : 2 ≤ n) :
    P (2 ^ n) (2 ^ n) = eB * X ^ 2 ^ n * (X + 1) ^ (2 ^ n - 3) := by
  have hm : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hF := frob_uQ n
  have hT := frob_tu n
  have hG := G_mul (2 ^ n)
  set m := 2 ^ n with hmdef
  have hV : (X + 1 : (ZMod 2)[X]) ^ m = (X + 1) ^ 3 * (X + 1) ^ (m - 3) := by
    rw [← pow_add]; congr 1; omega
  have hu : ((X + 1 : (ZMod 2)[X]) ^ 3) ≠ 0 := pow_ne_zero _ (X_add_C_ne_zero 1)
  apply mul_left_cancel₀ hu
  simp only [P, Nat.sub_self, mul_zero, pow_zero, one_mul]
  rw [mul_pow, hV] at hT
  rw [hV] at hF
  linear_combination (norm := (ring_nf <;> reduce_mod_char)) eB * hF - eB * hT + eB * hG

/-- **Theorem F (helper form).**  For `m = 2^n ≥ 4`, `e_B t^m (t+1)^(m−3)` has exact period
`2m`. -/
theorem fU_minimalPeriod (n : ℕ) (hn : 2 ≤ n) :
    minimalPeriod fU (eB * X ^ 2 ^ n * (X + 1) ^ (2 ^ n - 3)) = 2 ^ (n + 1) := by
  set x₀ := eB * X ^ 2 ^ n * (X + 1) ^ (2 ^ n - 3) with hx₀
  have hm : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 : fU^[2 ^ n] x₀ = P (2 ^ n) 0 := by
    have := fU_iterate_E (2 ^ n) 0 (eB * (X + 1) ^ (2 ^ n - 3))
    rw [hx₀, show eB * X ^ 2 ^ n * (X + 1) ^ (2 ^ n - 3)
      = X ^ (2 ^ n + 0) * (eB * (X + 1) ^ (2 ^ n - 3)) by ring, this]
    simp only [P, G]
    ring
  have h2 : fU^[2 ^ n] (P (2 ^ n) 0) = x₀ := by
    rw [P_iterate n _ hn le_rfl, P_last n hn]
  have hper : IsPeriodicPt fU (2 ^ (n + 1)) x₀ := by
    show fU^[2 ^ (n + 1)] x₀ = x₀
    rw [pow_succ, mul_two, iterate_add_apply, h1, h2]
  have hne : fU^[2 ^ n] x₀ ≠ x₀ := by
    rw [h1]
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp only [P, G, hx₀, eB, fQ, mul_zero, add_zero, eval_mul, eval_pow, eval_add, eval_X,
      eval_one] at this
    rw [zero_pow (by positivity)] at this
    norm_num at this
  obtain ⟨i, hi, hmp⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hper.minimalPeriod_dvd
  rcases (show i = n + 1 ∨ i ≤ n by omega) with rfl | hi'
  · exact hmp
  · exfalso
    apply hne
    have : minimalPeriod fU x₀ ∣ 2 ^ n := hmp ▸ Nat.pow_dvd_pow 2 hi'
    exact isPeriodicPt_iff_minimalPeriod_dvd.mpr this

end CollatzMoonshot.Amusical.FFTwin
