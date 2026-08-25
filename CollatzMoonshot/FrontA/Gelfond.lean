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

open Filter Topology Asymptotics

/-- `log n / √n → 0` (the sub-exponential factor in `lcmUpto_le` is beaten by any geometric base).
From `log =o[atTop] x^(1/2)`. -/
theorem log_div_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log n / Real.sqrt n) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h2 := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with n _
  simp only [Function.comp_apply, Real.sqrt_eq_rpow]

/-- **`lcm(1..n)·cⁿ → 0` for `0 ≤ c < 1/4` (leg-1 assembly brick).**  `lcmUpto n ≤ 4ⁿ·e^{2√n·log n}`
(`lcmUpto_le`), so `lcm·cⁿ ≤ (4c)ⁿ·e^{2√n·log n} = exp(n·log(4c) + 2√n·log n)`; the exponent `→ −∞`
because `4c < 1` makes the linear term dominate the sub-exponential `2√n·log n` (`log_div_sqrt_
tendsto_zero`).  This is exactly the "the geometric remainder beats the denominator" limit that turns a
small-nonzero-integer-combination sequence into an irrationality/effective-measure conclusion — used
for `log 2` now (`Legendre.legendre_log_two_small`) and reused, two-kernel-wise, by leg 3. -/
theorem lcmUpto_mul_geom_tendsto_zero {c : ℝ} (hc0 : 0 ≤ c) (hc : 4 * c < 1) :
    Tendsto (fun n : ℕ => (Nat.lcmUpto n : ℝ) * c ^ n) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hc0 with hc00 | hc0'
  · -- c = 0: eventually zero
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← hc00, zero_pow (by omega), mul_zero]
  · -- 0 < c
    set b := 4 * c with hb
    have hb0 : 0 < b := by rw [hb]; linarith
    have hlogb : Real.log b < 0 := Real.log_neg hb0 hc
    -- exponent → atBot
    have hh : Tendsto (fun n : ℕ => (n : ℝ) * Real.log b + 2 * Real.sqrt n * Real.log n)
        atTop atBot := by
      have hK : (0 : ℝ) < -Real.log b / 4 := by linarith
      have hev : ∀ᶠ n : ℕ in atTop, Real.log n / Real.sqrt n < -Real.log b / 4 :=
        log_div_sqrt_tendsto_zero.eventually (Iio_mem_nhds hK)
      have hle : ∀ᶠ n : ℕ in atTop,
          (n : ℝ) * Real.log b + 2 * Real.sqrt n * Real.log n ≤ (n : ℝ) * (Real.log b / 2) := by
        filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
        have hsqrt : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
        have hsn : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (by positivity)
        have key : 2 * Real.sqrt n * Real.log n
            = 2 * (n : ℝ) * (Real.log n / Real.sqrt n) := by
          rw [show 2 * (n : ℝ) * (Real.log n / Real.sqrt n)
                = 2 * Real.log n * ((n : ℝ) / Real.sqrt n) from by ring, Real.div_sqrt]
          ring
        have h2 : 2 * (n : ℝ) * (Real.log n / Real.sqrt n) ≤ -(n : ℝ) * Real.log b / 2 := by
          calc 2 * (n : ℝ) * (Real.log n / Real.sqrt n)
              ≤ 2 * (n : ℝ) * (-Real.log b / 4) :=
                mul_le_mul_of_nonneg_left (le_of_lt hn) (by positivity)
            _ = -(n : ℝ) * Real.log b / 2 := by ring
        have hbridge : (n : ℝ) * (Real.log b / 2) = (n : ℝ) * Real.log b / 2 := by ring
        rw [key]; linarith [h2, hbridge]
      refine tendsto_atBot_mono' atTop hle ?_
      exact (tendsto_natCast_atTop_atTop).atTop_mul_const_of_neg (by linarith)
    -- g n = exp(exponent) → 0, and squeeze
    have hg : Tendsto (fun n : ℕ => b ^ n * Real.exp (2 * Real.sqrt n * Real.log n))
        atTop (𝓝 0) := by
      have hexp : (fun n : ℕ => b ^ n * Real.exp (2 * Real.sqrt n * Real.log n))
          = fun n : ℕ => Real.exp ((n : ℝ) * Real.log b + 2 * Real.sqrt n * Real.log n) := by
        funext n
        rw [Real.exp_add]
        congr 1
        rw [Real.exp_nat_mul, Real.exp_log hb0]
      rw [hexp]
      exact Real.tendsto_exp_atBot.comp hh
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
    · filter_upwards with n; positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      calc (Nat.lcmUpto n : ℝ) * c ^ n
          ≤ (4 ^ n * Real.exp (2 * Real.sqrt n * Real.log n)) * c ^ n :=
            mul_le_mul_of_nonneg_right (lcmUpto_le n hn) (pow_nonneg hc0 n)
        _ = b ^ n * Real.exp (2 * Real.sqrt n * Real.log n) := by rw [hb, mul_pow]; ring

end CollatzMoonshot.FrontA
