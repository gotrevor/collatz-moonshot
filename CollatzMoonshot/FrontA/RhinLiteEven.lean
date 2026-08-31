/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.RhinLiteMaximum

/-!
# The even Rhin-lite subsequence

This file lifts the denominator-1000 base kernel to the original indices `N = 2000t`.
All six exponents are even, so the two remainder integrands are nonnegative and the
base maximum estimate can be raised without cancellation.
-/

namespace CollatzMoonshot.FrontA

open Polynomial Set

/-- Substituting `-X` negates each coefficient by the parity of its index. -/
theorem coeff_comp_neg_X (p : ℚ[X]) (k : ℕ) :
    (p.comp (-X)).coeff k = (-1) ^ k * p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, coeff_add, hp, hq, mul_add]
  | monomial n a =>
      rw [monomial_comp, coeff_C_mul,
        show (-X : ℚ[X]) ^ n = C ((-1 : ℚ) ^ n) * X ^ n by
          rw [neg_eq_neg_one_mul, mul_pow]; simp,
        coeff_C_mul, coeff_X_pow, coeff_monomial]
      by_cases h : n = k
      · subst h; simp [mul_comm]
      · rw [if_neg h, if_neg (by simpa [eq_comm] using h)]; ring

/-- The original index on the even Rhin-lite subsequence. -/
def rhinLiteEvenIndex (t : ℕ) : ℕ := 2 * rhinLiteScale * t

/-- The original signed six-factor polynomial at `N = 2000t`. -/
noncomputable def rhinLiteEvenPolynomial (t : ℕ) : ℚ[X] :=
  (X - C 3) ^ (2 * rhinLiteW1 * t) *
    (X - C 2) ^ (2 * rhinLiteW2 * t) *
    (X - C 4) ^ (2 * rhinLiteW3 * t) *
    (C 5 * X - C 12) ^ (2 * rhinLiteW4 * t) *
    (C 17 * X ^ 2 - C 102 * X + C 144) ^ (2 * rhinLiteW5 * t) *
    (C 19 * X ^ 2 - C 108 * X + C 144) ^ (2 * rhinLiteW6 * t)

/-- The signed polynomial has the required exact degree `2N`. -/
theorem rhinLiteEvenPolynomial_natDegree (t : ℕ) :
    (rhinLiteEvenPolynomial t).natDegree = 2 * rhinLiteEvenIndex t := by
  rw [rhinLiteEvenPolynomial, rhinLiteEvenIndex]
  compute_degree!
  all_goals simp only [rhinLiteScale, rhinLiteW1, rhinLiteW2, rhinLiteW3,
    rhinLiteW4, rhinLiteW5, rhinLiteW6]
  all_goals omega

/-- Negating the variable turns the even signed polynomial into the positive polynomial
already used for the coefficient certificates, at parameter `2t`. -/
theorem rhinLiteEvenPolynomial_comp_neg_X (t : ℕ) :
    (rhinLiteEvenPolynomial t).comp (-X) = rhinLitePositive (2 * t) := by
  have keyN : ∀ (A B : ℚ[X]) (w : ℕ), A.comp (-X) = -B →
      (A ^ (2 * w * t)).comp (-X) = B ^ (w * (2 * t)) := by
    intro A B w h
    rw [pow_comp, h, show 2 * w * t = 2 * (w * t) by ring,
      show w * (2 * t) = 2 * (w * t) by ring, pow_mul (-B) 2 (w * t),
      pow_mul B 2 (w * t), neg_sq]
  have keyP : ∀ (A B : ℚ[X]) (w : ℕ), A.comp (-X) = B →
      (A ^ (2 * w * t)).comp (-X) = B ^ (w * (2 * t)) := by
    intro A B w h
    rw [pow_comp, h, show 2 * w * t = w * (2 * t) by ring]
  rw [rhinLiteEvenPolynomial]
  simp only [mul_comp]
  rw [keyN (X - C 3) (rhinLiteLinear 3 1) rhinLiteW1
        (by simp [rhinLiteLinear, sub_comp]; ring),
      keyN (X - C 2) (rhinLiteLinear 2 1) rhinLiteW2
        (by simp [rhinLiteLinear, sub_comp]; ring),
      keyN (X - C 4) (rhinLiteLinear 4 1) rhinLiteW3
        (by simp [rhinLiteLinear, sub_comp]; ring),
      keyN (C 5 * X - C 12) (rhinLiteLinear 12 5) rhinLiteW4
        (by simp [rhinLiteLinear, sub_comp, mul_comp]; ring),
      keyP (C 17 * X ^ 2 - C 102 * X + C 144) (rhinLiteQuadratic 144 102 17) rhinLiteW5
        (by simp [rhinLiteQuadratic, rhinLiteLinear, sub_comp, add_comp, mul_comp, pow_comp];
            ring),
      keyP (C 19 * X ^ 2 - C 108 * X + C 144) (rhinLiteQuadratic 144 108 19) rhinLiteW6
        (by simp [rhinLiteQuadratic, rhinLiteLinear, sub_comp, add_comp, mul_comp, pow_comp];
            ring)]
  rw [rhinLitePositive]

/-- Because the central index is even, its signed coefficient is exactly the previously
certified positive coefficient at parameter `2t`. -/
theorem rhinLiteEvenPolynomial_centralCoeff (t : ℕ) :
    (rhinLiteEvenPolynomial t).coeff (rhinLiteEvenIndex t) =
      (rhinLitePositive (2 * t)).coeff (rhinLiteEvenIndex t) := by
  have h := congrArg (fun p : ℚ[X] => p.coeff (rhinLiteEvenIndex t))
    (rhinLiteEvenPolynomial_comp_neg_X t)
  simp only [coeff_comp_neg_X] at h
  rwa [show ((-1 : ℚ)) ^ (rhinLiteEvenIndex t) = 1 from by
      rw [rhinLiteEvenIndex]; exact Even.neg_one_pow ⟨rhinLiteScale * t, by ring⟩,
      one_mul] at h

/-- The actual central coefficient lies in the promised `17^N,18^N` band. -/
theorem rhinLiteEvenPolynomial_centralCoeff_bounds (t : ℕ) :
    (17 : ℚ) ^ rhinLiteEvenIndex t ≤
        (rhinLiteEvenPolynomial t).coeff (rhinLiteEvenIndex t) ∧
      (rhinLiteEvenPolynomial t).coeff (rhinLiteEvenIndex t) ≤
        (18 : ℚ) ^ rhinLiteEvenIndex t := by
  rw [rhinLiteEvenPolynomial_centralCoeff,
    show rhinLiteEvenIndex t = rhinLiteScale * (2 * t) by rw [rhinLiteEvenIndex]; ring]
  exact ⟨seventeen_pow_le_rhinLitePositive_coeff (2 * t),
    rhinLitePositive_coeff_le_eighteen_pow (2 * t)⟩

/-- The normalized pointwise remainder before its final `1/x` integration factor. -/
noncomputable def rhinLiteEvenNormalized (t : ℕ) (x : ℝ) : ℝ :=
  aeval x (rhinLiteEvenPolynomial t) / x ^ rhinLiteEvenIndex t

/-- A real base raised to an even power equals its absolute value raised to that power. -/
theorem even_base_pow_abs (a : ℝ) (m : ℕ) : a ^ (2 * m) = |a| ^ (2 * m) := by
  rw [pow_mul, pow_mul, ← sq_abs]

/-- Exact factorwise identification with the even power of the base absolute kernel. -/
theorem rhinLiteEvenNormalized_eq (t : ℕ) {x : ℝ} (hx : 0 < x) :
    rhinLiteEvenNormalized t x =
      (rhinLiteKernelAbs x / x ^ rhinLiteScale) ^ (2 * t) := by
  simp only [rhinLiteEvenNormalized, rhinLiteEvenPolynomial, map_mul, map_pow, map_sub,
    map_add, aeval_X, aeval_C, map_ofNat, eq_ratCast, Rat.cast_ofNat]
  rw [div_pow]
  simp only [rhinLiteKernelAbs, abs_pow, abs_mul]
  have mk : ∀ (a : ℝ) (w : ℕ), a ^ (2 * w * t) = |a| ^ (w * (2 * t)) := by
    intro a w
    rw [show 2 * w * t = 2 * (w * t) by ring, show w * (2 * t) = 2 * (w * t) by ring,
      even_base_pow_abs]
  rw [mk (x - 3) rhinLiteW1, mk (x - 2) rhinLiteW2, mk (x - 4) rhinLiteW3,
    mk (5 * x - 12) rhinLiteW4, mk (17 * x ^ 2 - 102 * x + 144) rhinLiteW5,
    mk (19 * x ^ 2 - 108 * x + 144) rhinLiteW6]
  simp only [rhinLiteFactor1, rhinLiteFactor2, rhinLiteFactor3, rhinLiteFactor4,
    rhinLiteFactor5, rhinLiteFactor6, rhinLiteEvenIndex]
  ring

/-- Every normalized even-subsequence integrand is nonnegative. -/
theorem rhinLiteEvenNormalized_nonneg (t : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ rhinLiteEvenNormalized t x := by
  rw [rhinLiteEvenNormalized_eq t hx, pow_mul]
  positivity

/-- Raising the global base theorem gives the exact pointwise decay at index `N`. -/
theorem rhinLiteEvenNormalized_le {t : ℕ} {x : ℝ} (hx : x ∈ Icc (2 : ℝ) 4) :
    rhinLiteEvenNormalized t x ≤ (9 / 40 : ℝ) ^ rhinLiteEvenIndex t := by
  rw [rhinLiteEvenNormalized_eq t (by linarith [hx.1]),
    show rhinLiteEvenIndex t = rhinLiteScale * (2 * t) by rw [rhinLiteEvenIndex]; ring,
    pow_mul (9 / 40 : ℝ) rhinLiteScale (2 * t)]
  exact pow_le_pow_left₀
    (div_nonneg (by rw [rhinLiteKernelAbs]; positivity)
      (pow_nonneg (by linarith [hx.1]) _))
    (rhinLiteKernelAbs_div_pow_le_on_Icc hx) (2 * t)

end CollatzMoonshot.FrontA
