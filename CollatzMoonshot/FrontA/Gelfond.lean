/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Toward the Gelfond effective measure of `log₂3` (denominator infrastructure)

The sole remaining input behind the two-block exclusion is `sep_two_three` (`PowSeparation.lean`),
now reduced *sorry-free* (`sep_two_three_of_gelfond_measure`) to ONE uniform bound
`hmeas : ∀ near-critical k ≥ 130, 3^k ≤ (2^m − 3^k)·k^6`.  This is exactly the **classical Gelfond
1935 effective bound on the distance between powers of 2 and 3** (linear forms in two logarithms;
explicit constants in Bennett–Bugeaud, *Acta Arith.* 155 (2012), and Bugeaud's monograph §3.1), a
*polynomial* irrationality measure of `log₂3`.

## The construction skeleton (what `hmeas` needs, and where this file fits)

An effective irrationality measure of `log₂3` via the Padé / hypergeometric method builds, for each
degree `n`, an explicit rational linear form `Λ_n = A_n·log 2 + B_n·log 3 + C_n` (equivalently a
Padé-type approximant to the relevant power/log function) with **integer** numerators after clearing
denominators, then combines three estimates:

1. **Denominator bound** — the coefficients `A_n, B_n, C_n` become integers once multiplied by
   `lcm(1,…,n)` (or a Chudnovsky-refined divisor of it); a finite measure needs
   `lcm(1,…,n) ≤ D^n` for a fixed base `D`.  **This file supplies exactly that** (`lcmUpto_le`,
   from mathlib's Chebyshev `ψ(n) = log lcm(1..n) ≤ log 4·n + o(n)`), confirming the denominator
   ingredient is already reachable in mathlib — one of the three legs of the construction.
2. **Remainder (upper) bound** — the analytic remainder `|Λ_n(z)|` decays geometrically
   (`≤ E^{-n}`), from the Padé integral representation.  *[not yet formalized — needs the source
   construction]*
3. **Non-vanishing / lower structure** — `Λ_n ≠ 0` and a two-term telescoping to isolate the linear
   form in the two logs.  *[not yet formalized]*

Assembling (1)+(2)+(3) gives `|m·log 2 − k·log 3| ≥ c·H^{-κ}` (polynomial), whence `hmeas`.  Legs 2–3
are the genuine multi-lap GO grind (no mathlib support; source construction pending — see
`ON-LINE-REQUEST.md`).  This file lands leg 1.
-/

open Chebyshev Real

namespace CollatzMoonshot.FrontA

/-- **Denominator growth `lcm(1,…,n) ≤ 4^n · e^{2√n·log n}` (leg 1 of the Gelfond construction).**
The Padé/hypergeometric approximants to `log₂3` have coefficients whose denominators divide
`lcm(1,…,n)`; a *finite* (polynomial) irrationality measure requires this to grow at most like a
fixed exponential.  Direct from mathlib's Chebyshev estimate `ψ(n) = log lcm(1..n) ≤ log 4·n + 2√n·log n`.
(The sub-exponential factor `e^{2√n·log n}` is absorbed by the geometric main term in the assembly.) -/
theorem lcmUpto_le (n : ℕ) (hn : 1 ≤ n) :
    (Nat.lcmUpto n : ℝ) ≤ 4 ^ n * Real.exp (2 * Real.sqrt n * Real.log n) := by
  have hpos : (0 : ℝ) < (Nat.lcmUpto n : ℝ) := by exact_mod_cast Nat.lcmUpto_pos n
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log (Nat.lcmUpto n)
      ≤ (n : ℝ) * Real.log 4 + 2 * Real.sqrt n * Real.log n := by
    rw [← Chebyshev.psi_eq_log_lcmUpto]
    have h := Chebyshev.psi_le hnR
    linarith [h]
  have hexp := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log hpos, Real.exp_add, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 4)] at hexp

end CollatzMoonshot.FrontA
