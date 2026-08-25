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

/-- **Vanishing at `0` to order `n` (Padé contact).**  For `m < n`, the `m`-th derivative of
`x^n (1-x)^n` vanishes at `0`.  Makes the boundary terms of the integration-by-parts identity (that
turns `∫₀¹ P_n·f` into the linear form) vanish. -/
lemma shiftedLegendre_poly_eval_zero_eq_zero (n : ℕ) {m : ℕ} (h : m < n) :
    eval 0 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finset_sum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; left
  simp only [Polynomial.iterate_derivative_X_pow_eq_smul, eval_smul, eval_pow, eval_X, smul_eq_mul,
    mul_eq_zero, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt, pow_eq_zero_iff', ne_eq,
    true_and]
  right
  suffices n - (m - x) > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  rw [Nat.lt_add_one_iff] at hx
  calc
    m - x ≤ m := by simp
    _ < n := h

/-- **Vanishing at `1` to order `n` (Padé contact).**  For `m < n`, the `m`-th derivative of
`x^n (1-x)^n` vanishes at `1`.  The companion boundary condition. -/
lemma shiftedLegendre_poly_eval_one_eq_zero (n : ℕ) {m : ℕ} (h : m < n) :
    eval 1 ((⇑derivative)^[m] (X ^ n * (1 - X) ^ n) : ℝ[X]) = 0 := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finset_sum]
  apply Finset.sum_eq_zero
  intro x hx
  simp_all only [Nat.succ_eq_add_one, Finset.mem_range, nsmul_eq_mul, eval_mul, eval_natCast,
    mul_eq_zero, Nat.cast_eq_zero]
  right; right
  rw [show (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) by simp,
    Polynomial.iterate_derivative_comp_one_sub_X (p := X ^ n),
    Polynomial.iterate_derivative_X_pow_eq_smul]
  simp only [smul_comp, pow_comp, X_comp, Algebra.mul_smul_comm, eval_smul, eval_mul, eval_pow,
    eval_neg, eval_one, eval_sub, eval_X, sub_self, smul_eq_mul, mul_eq_zero, Nat.cast_eq_zero,
    Nat.descFactorial_eq_zero_iff_lt, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, false_and,
    true_and, false_or]
  right
  suffices n - x > 0 by linarith
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  linarith

/-- **Single integration-by-parts step against a Legendre-derivative polynomial.**  If a polynomial
`p` vanishes at both endpoints, then `∫₀¹ (p')·g = −∫₀¹ p·g'` (the boundary term dies).  This is the
inductive engine of the `n`-fold Legendre IBP identity. -/
private lemma legendre_ibp_step (p : ℝ[X]) (g g' : ℝ → ℝ)
    (hp0 : eval 0 p = 0) (hp1 : eval 1 p = 0)
    (hg : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' y) y)
    (hg' : ContinuousOn g' (Set.uIcc (0 : ℝ) 1)) :
    ∫ y in (0 : ℝ)..1, eval y (derivative p) * g y
      = - ∫ y in (0 : ℝ)..1, eval y p * g' y := by
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y => eval y p) (u' := fun y => eval y (derivative p)) (v := g) (v' := g')
    (fun y _ => p.hasDerivAt y) hg
    ((Polynomial.continuous (derivative p)).intervalIntegrable 0 1)
    hg'.intervalIntegrable
  rw [hp0, hp1] at key
  simp only [zero_mul, sub_zero, zero_sub] at key
  linarith [key]

/-- **Legendre integration-by-parts identity (leg 2 core).**  For any `f` whose iterated derivatives
`deriv^[k] f` (`k ≤ n`) are continuous on `[0,1]` and differentiable there (`k < n`),
`∫₀¹ P_n(y)·f(y) dy = ((-1)^n / n!) · ∫₀¹ y^n(1-y)^n · f⁽ⁿ⁾(y) dy`, where `P_n = shiftedLegendre n`.
Proof: `n`-fold integration by parts (`legendre_ibp_step`); every boundary term vanishes by
`shiftedLegendre_poly_eval_{zero,one}_eq_zero`.  Specialized to a Möbius kernel `f(y)=1/(1−(1−c)y)`
this yields the linear form `A_n + B_n·log c` with geometrically small remainder — the analytic heart
of Rhin's effective measure of `log₂3` (see `Gelfond.lean`). -/
theorem integral_shiftedLegendre_mul_eq (n : ℕ) (f : ℝ → ℝ)
    (hcont : ∀ k, k ≤ n → ContinuousOn (deriv^[k] f) (Set.uIcc (0 : ℝ) 1))
    (hderiv : ∀ k, k < n → ∀ y ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (deriv^[k] f) (deriv^[k + 1] f y) y) :
    ∫ y in (0 : ℝ)..1, eval y (shiftedLegendre n) * f y
      = ((-1) ^ n / n !) * ∫ y in (0 : ℝ)..1, (y ^ n * (1 - y) ^ n) * (deriv^[n] f) y := by
  have aux : ∀ m, m ≤ n →
      ∫ y in (0 : ℝ)..1, eval y (derivative^[n] ((X : ℝ[X]) ^ n * (1 - X) ^ n)) * f y
        = (-1) ^ m * ∫ y in (0 : ℝ)..1,
            eval y (derivative^[n - m] ((X : ℝ[X]) ^ n * (1 - X) ^ n)) * (deriv^[m] f) y := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ j ih =>
        intro hj
        have hjn : j < n := hj
        rw [ih (le_of_lt hjn)]
        have hidx : derivative^[n - j] ((X : ℝ[X]) ^ n * (1 - X) ^ n)
            = derivative (derivative^[n - (j + 1)] ((X : ℝ[X]) ^ n * (1 - X) ^ n)) := by
          have hnj : n - j = (n - (j + 1)) + 1 := by omega
          rw [hnj, Function.iterate_succ_apply']
        have hp := legendre_ibp_step (derivative^[n - (j + 1)] ((X : ℝ[X]) ^ n * (1 - X) ^ n))
          (deriv^[j] f) (deriv^[j + 1] f)
          (shiftedLegendre_poly_eval_zero_eq_zero n (by omega))
          (shiftedLegendre_poly_eval_one_eq_zero n (by omega))
          (hderiv j hjn) (hcont (j + 1) hj)
        rw [hidx, hp, pow_succ]
        ring
  have H := aux n le_rfl
  rw [Nat.sub_self] at H
  simp only [Function.iterate_zero, id_eq] at H
  have hUval : (fun y : ℝ => eval y ((X : ℝ[X]) ^ n * (1 - X) ^ n) * (deriv^[n] f) y)
      = fun y : ℝ => (y ^ n * (1 - y) ^ n) * (deriv^[n] f) y := by
    funext y; simp [eval_mul, eval_pow]
  rw [hUval] at H
  -- pull the constant `(n!)⁻¹` out of the shiftedLegendre integral
  have hLHS : (fun y : ℝ => eval y (shiftedLegendre n) * f y)
      = fun y : ℝ => (n ! : ℝ)⁻¹ * (eval y (derivative^[n] ((X : ℝ[X]) ^ n * (1 - X) ^ n)) * f y) := by
    funext y; simp only [shiftedLegendre, eval_mul, eval_C]; ring
  rw [hLHS, intervalIntegral.integral_const_mul, H]
  ring

end CollatzMoonshot.FrontA
