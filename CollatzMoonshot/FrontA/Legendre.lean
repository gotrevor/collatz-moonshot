/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Shifted Legendre polynomials — approximant backbone for the Gelfond `log₂3` measure (leg 2 start)

Rhin's effective linear-independence measure of `{1, log 2, log 3}` (< 7.616; the classical object
behind `sep_two_three`, see `PowSeparation.lean` / `Gelfond.lean`) is built from Padé/Legendre-type
approximants: integrals `∫₀¹ P_n(x)·(smooth) dx` where `P_n` is the shifted Legendre polynomial
`P_n = (n!)⁻¹ · (d/dx)^n (x^n (1-x)^n)`.  The two facts a measure proof leans on first are (i) the
explicit sum form and (ii) **integer coefficients** (which control the denominator via `lcm(1..n)`,
leg 1 = `Gelfond.lcmUpto_le`).

This module ports those two facts (`shiftedLegendre_eq_sum`, `shiftedLegendre_eq_int_poly`) from the
verified ζ(3)-irrationality development (`~/src/reservoir/ahhwuhu/zeta_3_irrational`), adapting to the
current toolchain.  These are the correct, kernel-checked backbone of the log-measure construction;
the analytic remainder-decay integral (leg 2 proper) and non-vanishing (leg 3) build on them once the
exact Rhin kernel lands (see `ON-LINE-REQUEST.md`).
-/

open scoped Nat
open BigOperators Finset Polynomial

namespace CollatzMoonshot.FrontA

variable {R : Type*}

/-- `shiftedLegendre n` is the shifted Legendre polynomial `(n!)⁻¹ · (d/dx)^n (x^n (1-x)^n)`. -/
noncomputable def shiftedLegendre (n : ℕ) : ℝ[X] :=
  C (n ! : ℝ)⁻¹ * derivative^[n] (X ^ n * (1 - X) ^ n)

private lemma Finsum_iterate_deriv [CommRing R] (k : ℕ) (h : ℕ → ℕ) :
    derivative^[k] (∑ m ∈ Finset.range (k + 1), (h m) • ((-1) ^ m : R[X]) * X ^ (k + m)) =
    ∑ m ∈ Finset.range (k + 1), (h m) • (-1) ^ m * derivative^[k] (X ^ (k + m)) := by
  induction' k + 1 with n hn
  · simp only [Finset.range_zero, Finset.sum_empty, iterate_map_zero]
  · rw [Finset.sum_range, Finset.sum_range, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at *
    simp only [Fin.coe_castSucc, Fin.val_last, iterate_map_add, hn, add_right_inj]
    rw [nsmul_eq_mul, mul_assoc, ← nsmul_eq_mul, Polynomial.iterate_derivative_smul, nsmul_eq_mul,
      mul_assoc]
    rcases n.even_or_odd with (hn1 | hn2)
    · simp_all only [nsmul_eq_mul, Int.even_coe_nat, Even.neg_pow, one_pow, one_mul]
    · rw [Odd.neg_one_pow]
      simp only [neg_mul, one_mul, iterate_map_neg, mul_neg]
      exact_mod_cast hn2

/-- The expansion of `shiftedLegendre n` as an explicit polynomial sum. -/
theorem shiftedLegendre_eq_sum (n : ℕ) : shiftedLegendre n = ∑ k ∈ Finset.range (n + 1),
    C ((-1) ^ k : ℝ) * (Nat.choose n k : ℝ[X]) * (Nat.choose (n + k) n : ℝ[X]) * X ^ k := by
  have h : ((X : ℝ[X]) - X ^ 2) ^ n =
      ∑ m ∈ range (n + 1), n.choose m • (- 1) ^ m * X ^ (n + m) := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    congr! 1 with m hm
    rw [neg_pow, pow_two, mul_pow, ← mul_assoc, mul_comm, mul_assoc, pow_mul_pow_sub, mul_assoc,
      ← pow_add, ← mul_assoc, nsmul_eq_mul, add_comm]
    rw [Finset.mem_range] at hm
    linarith
  rw [shiftedLegendre, ← mul_pow, mul_one_sub, ← pow_two, h, Finsum_iterate_deriv,
    Finset.mul_sum]
  congr! 1 with x _
  rw [← mul_assoc, Polynomial.iterate_derivative_X_pow_eq_smul, Nat.descFactorial_eq_div
    (by omega), show n + x - n = x by omega, nsmul_eq_mul, ← mul_assoc, mul_assoc,
    mul_comm]
  simp only [Int.reduceNeg, map_pow, map_neg, map_one]
  rw [Algebra.smul_def, algebraMap_eq, map_natCast, ← mul_assoc, ← mul_assoc, add_comm,
    Nat.add_choose, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_comm]
  nth_rewrite 5 [mul_comm]
  congr 1
  nth_rewrite 2 [mul_comm]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  congr 1
  nth_rewrite 3 [mul_comm]
  congr 1
  apply Polynomial.ext
  intro m
  simp only [one_div, coeff_mul_C, coeff_natCast_ite, Nat.cast_ite, CharP.cast_eq_zero, ite_mul,
    zero_mul]
  by_cases h : m = 0
  · simp only [h, ↓reduceIte]
    rw [Nat.cast_div]
    · rw [← one_div, ← div_mul_eq_div_mul_one_div]
      norm_cast
      rw [Nat.cast_div]
      · exact Nat.factorial_mul_factorial_dvd_factorial_add x n
      · norm_cast
        apply mul_ne_zero (Nat.factorial_ne_zero x) (Nat.factorial_ne_zero n)
    · exact Nat.factorial_dvd_factorial (by omega)
    · norm_cast; exact Nat.factorial_ne_zero x
  · simp only [h, ↓reduceIte]

/-- **`shiftedLegendre n` is an integer polynomial.**  Coefficients
`(-1)^k · C(n,k) · C(n+k,n) ∈ ℤ`; this is the integrality that lets `lcm(1..n)` (leg 1) clear all
denominators of the approximant's linear form. -/
lemma shiftedLegendre_eq_int_poly (n : ℕ) : ∃ a : ℕ → ℤ, shiftedLegendre n =
    ∑ k ∈ Finset.range (n + 1), (a k : ℝ[X]) * X ^ k := by
  simp_rw [shiftedLegendre_eq_sum]
  use fun k => (- 1) ^ k * (Nat.choose n k) * (Nat.choose (n + k) n)
  congr! 1 with x
  push_cast
  simp only [map_pow, map_neg, map_one]

end CollatzMoonshot.FrontA
