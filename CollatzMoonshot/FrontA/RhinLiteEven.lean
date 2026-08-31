/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.RhinLiteMaximum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

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

/-! ## Interval-integral consequences on `[2,3]` and `[3,4]` -/

open MeasureTheory

/-- The absolute kernel is a continuous real function. -/
theorem continuous_rhinLiteKernelAbs : Continuous rhinLiteKernelAbs := by
  unfold rhinLiteKernelAbs rhinLiteFactor1 rhinLiteFactor2 rhinLiteFactor3 rhinLiteFactor4
    rhinLiteFactor5 rhinLiteFactor6
  fun_prop

/-- The normalized even integrand is continuous on `[2,4]`. -/
theorem continuousOn_rhinLiteEvenNormalized (t : ℕ) :
    ContinuousOn (rhinLiteEvenNormalized t) (Icc (2 : ℝ) 4) := by
  have hg : ContinuousOn
      (fun x => (rhinLiteKernelAbs x / x ^ rhinLiteScale) ^ (2 * t)) (Icc (2 : ℝ) 4) := by
    apply ContinuousOn.pow
    apply ContinuousOn.div continuous_rhinLiteKernelAbs.continuousOn
      (continuous_pow rhinLiteScale).continuousOn
    intro x hx
    exact pow_ne_zero _ (by linarith [hx.1] : x ≠ 0)
  exact hg.congr (fun x hx => rhinLiteEvenNormalized_eq t (by linarith [hx.1]))

/-- The normalized even integrand is interval-integrable on any subinterval of `[2,4]`. -/
theorem intervalIntegrable_rhinLiteEvenNormalized (t : ℕ) {a b : ℝ}
    (ha : 2 ≤ a) (hb : b ≤ 4) (hab : a ≤ b) :
    IntervalIntegrable (rhinLiteEvenNormalized t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact (continuousOn_rhinLiteEvenNormalized t).mono (Icc_subset_Icc ha hb)

/-- **Interval upper bound.** Each remainder integral is at most the interval length times the
pointwise decay `(9/40)^N`. -/
theorem rhinLiteEvenIntegral_le (t : ℕ) {a b : ℝ}
    (ha : 2 ≤ a) (hb : b ≤ 4) (hab : a ≤ b) :
    ∫ x in a..b, rhinLiteEvenNormalized t x ≤
      (b - a) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t := by
  have hbound := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_rhinLiteEvenNormalized t ha hb hab)
    (intervalIntegrable_const)
    (fun x hx => rhinLiteEvenNormalized_le
      ⟨le_trans ha hx.1, le_trans hx.2 hb⟩)
  simpa [mul_comm] using hbound

/-- The absolute kernel is strictly positive wherever all six factors are nonzero. -/
theorem rhinLiteKernelAbs_pos {x : ℝ}
    (h1 : rhinLiteFactor1 x ≠ 0) (h2 : rhinLiteFactor2 x ≠ 0) (h3 : rhinLiteFactor3 x ≠ 0)
    (h4 : rhinLiteFactor4 x ≠ 0) (h5 : rhinLiteFactor5 x ≠ 0) (h6 : rhinLiteFactor6 x ≠ 0) :
    0 < rhinLiteKernelAbs x := by
  unfold rhinLiteKernelAbs
  have a1 := abs_pos.mpr h1; have a2 := abs_pos.mpr h2; have a3 := abs_pos.mpr h3
  have a4 := abs_pos.mpr h4; have a5 := abs_pos.mpr h5; have a6 := abs_pos.mpr h6
  positivity

/-- The normalized even integrand is strictly positive wherever all six factors are nonzero
(and `x > 0`). -/
theorem rhinLiteEvenNormalized_pos (t : ℕ) {x : ℝ} (hx : 0 < x)
    (h1 : rhinLiteFactor1 x ≠ 0) (h2 : rhinLiteFactor2 x ≠ 0) (h3 : rhinLiteFactor3 x ≠ 0)
    (h4 : rhinLiteFactor4 x ≠ 0) (h5 : rhinLiteFactor5 x ≠ 0) (h6 : rhinLiteFactor6 x ≠ 0) :
    0 < rhinLiteEvenNormalized t x := by
  rw [rhinLiteEvenNormalized_eq t hx]
  exact pow_pos (div_pos (rhinLiteKernelAbs_pos h1 h2 h3 h4 h5 h6) (pow_pos hx _)) _

/-- **Positivity via a positive subinterval.** If the integrand is strictly positive on some
`(c,d) ⊆ [a,b] ⊆ [2,4]`, the whole integral is strictly positive. -/
theorem rhinLiteEvenIntegral_pos_of_subinterval (t : ℕ) {a b c d : ℝ}
    (ha : 2 ≤ a) (hb : b ≤ 4) (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (hpos : ∀ x ∈ Ioo c d, 0 < rhinLiteEvenNormalized t x) :
    0 < ∫ x in a..b, rhinLiteEvenNormalized t x := by
  have hcd' : c ≤ d := le_of_lt hcd
  have hc4 : c ≤ 4 := le_trans hcd' (le_trans hdb hb)
  have h2c : 2 ≤ c := le_trans ha hac
  have h2d : 2 ≤ d := le_trans h2c hcd'
  have iac := intervalIntegrable_rhinLiteEvenNormalized t ha hc4 hac
  have icd := intervalIntegrable_rhinLiteEvenNormalized t h2c
    (le_trans hdb hb) hcd'
  have idb := intervalIntegrable_rhinLiteEvenNormalized t h2d hb hdb
  have poscd : 0 < ∫ x in c..d, rhinLiteEvenNormalized t x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on icd hpos hcd
  have nonneg_ac : 0 ≤ ∫ x in a..c, rhinLiteEvenNormalized t x :=
    intervalIntegral.integral_nonneg hac
      (fun x hx => rhinLiteEvenNormalized_nonneg t (by linarith [hx.1] : (0:ℝ) < x))
  have nonneg_db : 0 ≤ ∫ x in d..b, rhinLiteEvenNormalized t x :=
    intervalIntegral.integral_nonneg hdb
      (fun x hx => rhinLiteEvenNormalized_nonneg t (by linarith [hx.1, h2d] : (0:ℝ) < x))
  have split1 := intervalIntegral.integral_add_adjacent_intervals icd idb
  have split2 := intervalIntegral.integral_add_adjacent_intervals iac
    (icd.trans idb)
  linarith [split1, split2]

/-- **The `[2,3]` remainder integral is strictly positive.** -/
theorem rhinLiteEvenIntegral_pos_23 (t : ℕ) :
    0 < ∫ x in (2 : ℝ)..3, rhinLiteEvenNormalized t x := by
  refine rhinLiteEvenIntegral_pos_of_subinterval t (a := 2) (b := 3) (c := 13/5) (d := 14/5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  intro x hx
  obtain ⟨hc, hd⟩ := hx
  refine rhinLiteEvenNormalized_pos t (by linarith : (0:ℝ) < x) ?_ ?_ ?_ ?_ ?_ ?_
  · exact (show rhinLiteFactor1 x < 0 by unfold rhinLiteFactor1; linarith).ne
  · exact (show (0:ℝ) < rhinLiteFactor2 x by unfold rhinLiteFactor2; linarith).ne'
  · exact (show rhinLiteFactor3 x < 0 by unfold rhinLiteFactor3; linarith).ne
  · exact (show (0:ℝ) < rhinLiteFactor4 x by unfold rhinLiteFactor4; linarith).ne'
  · have h5 : rhinLiteFactor5 x < 0 := by
      unfold rhinLiteFactor5
      nlinarith [mul_nonneg (show (0:ℝ) ≤ 14/5 - x by linarith)
        (show (0:ℝ) ≤ x - 13/5 by linarith)]
    exact h5.ne
  · have h6 : rhinLiteFactor6 x < 0 := by
      unfold rhinLiteFactor6
      nlinarith [mul_nonneg (show (0:ℝ) ≤ 14/5 - x by linarith)
        (show (0:ℝ) ≤ x - 13/5 by linarith)]
    exact h6.ne

/-- **The `[3,4]` remainder integral is strictly positive.** -/
theorem rhinLiteEvenIntegral_pos_34 (t : ℕ) :
    0 < ∫ x in (3 : ℝ)..4, rhinLiteEvenNormalized t x := by
  refine rhinLiteEvenIntegral_pos_of_subinterval t (a := 3) (b := 4) (c := 19/5) (d := 39/10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  intro x hx
  obtain ⟨hc, hd⟩ := hx
  refine rhinLiteEvenNormalized_pos t (by linarith : (0:ℝ) < x) ?_ ?_ ?_ ?_ ?_ ?_
  · exact (show (0:ℝ) < rhinLiteFactor1 x by unfold rhinLiteFactor1; linarith).ne'
  · exact (show (0:ℝ) < rhinLiteFactor2 x by unfold rhinLiteFactor2; linarith).ne'
  · exact (show rhinLiteFactor3 x < 0 by unfold rhinLiteFactor3; linarith).ne
  · exact (show (0:ℝ) < rhinLiteFactor4 x by unfold rhinLiteFactor4; linarith).ne'
  · have h5 : (0:ℝ) < rhinLiteFactor5 x := by
      unfold rhinLiteFactor5
      nlinarith [mul_pos (show (0:ℝ) < x - 19/5 by linarith)
        (show (0:ℝ) < x - 3 by linarith)]
    exact h5.ne'
  · have h6 : (0:ℝ) < rhinLiteFactor6 x := by
      unfold rhinLiteFactor6
      nlinarith [mul_pos (show (0:ℝ) < x - 19/5 by linarith)
        (show (0:ℝ) < x - 3 by linarith)]
    exact h6.ne'

/-- **Interval nonnegativity.** Each remainder integral is nonnegative. -/
theorem rhinLiteEvenIntegral_nonneg (t : ℕ) {a b : ℝ}
    (ha : 2 ≤ a) (hb : b ≤ 4) (hab : a ≤ b) :
    0 ≤ ∫ x in a..b, rhinLiteEvenNormalized t x := by
  apply intervalIntegral.integral_nonneg hab
  intro x hx
  exact rhinLiteEvenNormalized_nonneg t (by linarith [hx.1] : (0 : ℝ) < x)

end CollatzMoonshot.FrontA
