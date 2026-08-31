/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.RhinLiteEven
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact integer log forms for the Rhin-lite remainder integrals

Objective 3 of `FRONT-A-RHIN-LITE-NEXT.md`.  The remainder integral
`∫_a^b H_N(x) / x^{N+1} dx` (with `(a,b) = (2,3)` or `(3,4)`, `H_N` the degree-`2N` integer
polynomial) expands monomial by monomial: the `x^N` term contributes the central coefficient
times `log(b/a)`, and every other term `x^j` (`j ≠ N`) contributes the rational value
`(b^{j-N} - a^{j-N})/(j-N)`.

This module begins with the elementary single-monomial integral identity, the arithmetic core
from which the two cleared integer log forms `A₁ + B·log(3/2)`, `A₂ + B·log(4/3)` (common `B`,
explicit clearing factor `D_N`) will be assembled.
-/

namespace CollatzMoonshot.FrontA

open MeasureTheory intervalIntegral Polynomial Finset

/-- **Single-monomial integral identity.**  For `0 < a ≤ b`, the integral of `x^j / x^{N+1}`
over `[a,b]` is the log term `log(b/a)` when `j = N`, and the rational value
`(b^{j-N} - a^{j-N})/(j-N)` otherwise. -/
theorem integral_monomial_div_pow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (j N : ℕ) :
    (∫ x in a..b, x ^ j / x ^ (N + 1)) =
      if j = N then Real.log (b / a)
      else (b ^ ((j : ℤ) - N) - a ^ ((j : ℤ) - N)) / ((j : ℤ) - N) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h; linarith
  have hcongr : (∫ x in a..b, x ^ j / x ^ (N + 1)) =
      ∫ x in a..b, x ^ ((j : ℤ) - ((N + 1 : ℕ) : ℤ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    show x ^ j / x ^ (N + 1) = x ^ ((j : ℤ) - ((N + 1 : ℕ) : ℤ))
    rw [zpow_sub₀ (ne_of_gt hxpos), zpow_natCast, zpow_natCast]
  rw [hcongr]
  by_cases hjN : j = N
  · subst hjN
    rw [if_pos rfl]
    simp only [show ((j : ℤ) - ((j + 1 : ℕ) : ℤ)) = (-1 : ℤ) by push_cast; ring, zpow_neg_one]
    exact integral_inv h0
  · rw [if_neg hjN, integral_zpow (Or.inr ⟨by
        intro hcon
        apply hjN
        have : (j : ℤ) = N := by push_cast at hcon ⊢; linarith [hcon]
        exact_mod_cast this, h0⟩),
      show ((j : ℤ) - ((N + 1 : ℕ) : ℤ) + 1) = (j : ℤ) - N by push_cast; ring]
    congr 1
    push_cast
    ring

/-- Interval-integrability of a single monomial-over-power term on `[a,b]` with `0 < a`. -/
theorem intervalIntegrable_monomial_div_pow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (j N : ℕ) :
    IntervalIntegrable (fun x => x ^ j / x ^ (N + 1)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (continuous_pow j).continuousOn (continuous_pow (N + 1)).continuousOn
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact pow_ne_zero _ (by linarith [hx.1] : x ≠ 0)

/-- **Full remainder-integral expansion.**  For any real polynomial `p` and `0 < a ≤ b`,
`∫_a^b p(x)/x^{N+1} dx` expands as the coefficient sum in which the `x^N` term carries
`log(b/a)` and every other term is rational. -/
theorem integral_poly_div_pow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (p : ℝ[X]) (N : ℕ) :
    (∫ x in a..b, p.eval x / x ^ (N + 1)) =
      ∑ j ∈ range (p.natDegree + 1),
        p.coeff j * (if j = N then Real.log (b / a)
          else (b ^ ((j : ℤ) - N) - a ^ ((j : ℤ) - N)) / ((j : ℤ) - N)) := by
  have hcongr : (∫ x in a..b, p.eval x / x ^ (N + 1)) =
      ∫ x in a..b, ∑ j ∈ range (p.natDegree + 1), p.coeff j * (x ^ j / x ^ (N + 1)) := by
    apply intervalIntegral.integral_congr
    intro x _
    show p.eval x / x ^ (N + 1) = ∑ j ∈ range (p.natDegree + 1), p.coeff j * (x ^ j / x ^ (N + 1))
    rw [eval_eq_sum_range, Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => mul_div_assoc _ _ _)
  rw [hcongr, intervalIntegral.integral_finsetSum
    (fun j _ => (intervalIntegrable_monomial_div_pow ha hab j N).const_mul _)]
  exact Finset.sum_congr rfl (fun j _ => by
    rw [intervalIntegral.integral_const_mul, integral_monomial_div_pow ha hab])

/-- **Log term split out.**  When `N ≤ deg p`, the remainder integral is the single log term
`coeff_N · log(b/a)` plus a rational tail summed over the other indices. -/
theorem integral_poly_div_pow_split {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (p : ℝ[X]) (N : ℕ)
    (hN : N ≤ p.natDegree) :
    (∫ x in a..b, p.eval x / x ^ (N + 1)) =
      p.coeff N * Real.log (b / a) +
        ∑ j ∈ (range (p.natDegree + 1)).erase N,
          p.coeff j * ((b ^ ((j : ℤ) - N) - a ^ ((j : ℤ) - N)) / ((j : ℤ) - N)) := by
  rw [integral_poly_div_pow ha hab,
    ← Finset.add_sum_erase _ _ (mem_range.mpr (by omega : N < p.natDegree + 1))]
  congr 1
  · rw [if_pos rfl]
  · exact Finset.sum_congr rfl (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)])

end CollatzMoonshot.FrontA
