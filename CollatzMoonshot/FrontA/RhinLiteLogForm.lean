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

open MeasureTheory intervalIntegral

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

end CollatzMoonshot.FrontA
