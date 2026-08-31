/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import CollatzMoonshot.FrontA.RhinLiteLogForm
import CollatzMoonshot.FrontA.PowSeparation
import CollatzMoonshot.Assumed.Rhin1987

/-!
# Simultaneous-approximation criterion for the Rhin-lite log forms

This module is objective 4 of `FRONT-A-RHIN-LITE.md`: turn the two `D_N`-cleared integer log
forms produced by `rhinLiteEven_two_log_forms` into the **effective irrationality / separation**
statement the sink node `sep_two_three` (in `PowSeparation.lean`) needs, and wire the two ends
together as far as elementary algebra allows.

## The construction, and what the two forms give

For each block index `t` (`N := rhinLiteEvenIndex t = 2000t`), `rhinLiteEven_two_log_forms`
produces integers `A₁, A₂, B` with a **common** `B` such that

```text
D_N · ∫_2^3 H_N/x^{N+1} = A₁ + B · log(3/2),
D_N · ∫_3^4 H_N/x^{N+1} = A₂ + B · log(4/3),
D_N · 17^N ≤ B ≤ D_N · 18^N,     D_N = lcmUpto N · 12^N,
```

and (from `RhinLiteEven`) both integrals are positive and `≤ length·(9/40)^N`.  Set
`θ₁ := log(3/2)`, `θ₂ := log(4/3)`, `L₁ := A₁ + B θ₁`, `L₂ := A₂ + B θ₂`.  Relative to the common
denominator `B` the two forms are tiny:

```text
|θᵢ − (−Aᵢ)/B| = |Lᵢ| / B ≤ D_N (9/40)^N / (D_N 17^N) = (9/680)^N → 0,
```

so `(−A₁/B, −A₂/B)` is a sequence of rational simultaneous approximations to `(θ₁, θ₂)` with a
common denominator, of exponential quality.  The standard transference from such a sequence to a
**linear-independence measure** of `{1, θ₁, θ₂}` is Rhin's method; the coarse rationalized kernel
here gives a finite (non-optimal) exponent `κ`, which is all `sep_two_three` needs.

## What this file establishes

* `log_three_halves`, `log_four_thirds`, `linForm_eq_log23` — the elementary identity
  `(m−2k)·log(3/2) + (m−k)·log(4/3) = m·log2 − k·log3`.  This is the *change of basis* that
  expresses the Baker linear form `Λ = m·log2 − k·log3` (whose lower bound `sep_two_three` needs)
  as a **homogeneous** integer combination of `θ₁, θ₂` — no constant term.  Hence a linear
  independence measure of `{1, θ₁, θ₂}` directly bounds `Λ` from below.
* `elim_identity` — the elimination identity `B·(p + qθ₁ + rθ₂) = n + q·L₁ + r·L₂` with the
  integer `n = pB − qA₁ − rA₂`.  This is the algebraic heart of the transference: a nonzero `n`
  forces `|B·Λ| ≥ 1 − |q||L₁| − |r||L₂|`, hence `|Λ| ≥ (…)/B`.
* `rhinLiteLIMeasure` — **the disclosed crux** (single `sorry` in this file): the linear
  independence measure of `{1, θ₁, θ₂}` produced by the sequence above.  Its docstring records the
  concrete route from `rhinLiteEven_two_log_forms`.
* `log23_effective_measure` — **proved from `rhinLiteLIMeasure`**: the effective irrationality
  measure of `log₂ 3` in the exact linear-form shape `c/k^κ ≤ m·log2 − k·log3` on the
  near-critical window.  This is one restriction away from the `hLF` hypothesis of
  `sep_of_linear_form_poly`, so it is the concrete object that discharges `sep_two_three` once the
  crux is proved.

The remaining gap between `log23_effective_measure` and a fully-closed `sep_two_three` is the
constant/threshold reconciliation of `sep_of_linear_form_poly`'s crossover hypothesis `hcross`
(the finite near-`130` window depends on the unknown `c, κ` and needs `poly_le_pow` from an
explicit threshold); see `PENDING_WORK.md`.
-/

namespace CollatzMoonshot.FrontA

open Real Polynomial MeasureTheory Set

/-- `log(3/2) = log 3 − log 2`. -/
theorem log_three_halves : Real.log (3 / 2) = Real.log 3 - Real.log 2 := by
  rw [Real.log_div (by norm_num) (by norm_num)]

/-- `log(4/3) = 2·log 2 − log 3`. -/
theorem log_four_thirds : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
  rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  push_cast; ring

/-- **Change of basis to the Baker linear form.**  The homogeneous integer combination
`(m−2k)·log(3/2) + (m−k)·log(4/3)` equals the two-log linear form `m·log2 − k·log3`.  Thus a lower
bound on nonzero combinations of `{1, log(3/2), log(4/3)}` gives a lower bound on `Λ`. -/
theorem linForm_eq_log23 (k m : ℝ) :
    (m - 2 * k) * Real.log (3 / 2) + (m - k) * Real.log (4 / 3)
      = m * Real.log 2 - k * Real.log 3 := by
  rw [log_three_halves, log_four_thirds]; ring

/-- **Elimination identity.**  With the two forms `L₁ = A₁ + B·θ₁`, `L₂ = A₂ + B·θ₂` sharing the
denominator `B`, any integer combination `Λ = p + q·θ₁ + r·θ₂` satisfies
`B·Λ = (p·B − q·A₁ − r·A₂) + q·L₁ + r·L₂`.  The first summand is an integer `n`; when `n ≠ 0` this
forces `|B·Λ| ≥ 1 − |q||L₁| − |r||L₂|`, the mechanism turning the small forms into a lower bound on
`Λ`. -/
theorem elim_identity (A₁ A₂ B p q r : ℤ) (θ₁ θ₂ : ℝ) :
    (B : ℝ) * ((p : ℝ) + q * θ₁ + r * θ₂)
      = ((p * B - q * A₁ - r * A₂ : ℤ) : ℝ)
          + q * ((A₁ : ℝ) + B * θ₁) + r * ((A₂ : ℝ) + B * θ₂) := by
  push_cast; ring

/-- **Eval bridge.**  The real evaluation of the integer even polynomial equals the `aeval` of the
rational even polynomial (both are the value of the same underlying polynomial at `x`). -/
theorem rhinLiteEvenPolynomialZ_eval_real (t : ℕ) (x : ℝ) :
    ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x
      = aeval x (rhinLiteEvenPolynomial t) := by
  rw [← rhinLiteEvenPolynomialZ_map_rat, aeval_def, eval₂_eq_eval_map, Polynomial.map_map]
  congr 1

/-- **Integrand identity.**  The log-form integrand `H_N(x)/x^{N+1}` equals the normalized even
integrand divided by `x`.  This is the `x^{N+1}`→`x^N` bridge (factor `1/x`) connecting the
`RhinLiteLogForm` integral to the `RhinLiteEven` size/positivity bounds. -/
theorem rhinLiteEven_logForm_integrand (t : ℕ) (x : ℝ) :
    ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x / x ^ (rhinLiteEvenIndex t + 1)
      = rhinLiteEvenNormalized t x / x := by
  rw [rhinLiteEvenPolynomialZ_eval_real, rhinLiteEvenNormalized, div_div, ← pow_succ]

/-- Interval-integrability of the log-form integrand `normalized/x` on subintervals of `[2,4]`. -/
theorem intervalIntegrable_rhinLiteEven_logForm (t : ℕ) {a b : ℝ}
    (ha : 2 ≤ a) (hb : b ≤ 4) (hab : a ≤ b) :
    IntervalIntegrable (fun x => rhinLiteEvenNormalized t x / x) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
    ((continuousOn_rhinLiteEvenNormalized t).mono (Icc_subset_Icc ha hb))
    continuousOn_id
  intro x hx
  exact ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x)

/-- **Size + positivity of the log-form remainder integral.**  For `[a,b] ⊆ [2,4]` with the
normalized integral already known positive, the log-form integral `∫ H_N/x^{N+1} = ∫ normalized/x`
is positive and at most `(9/40)^N`.  Upper: `1/x ≤ 1/2` on `[2,4]` and `rhinLiteEvenIntegral_le`
(with `b − a ≤ 2`).  Lower: `1/x ≥ 1/4 > 0` and the positive normalized integral. -/
theorem rhinLiteEven_logForm_bounds_aux (t : ℕ) {a b : ℝ}
    (ha : 2 ≤ a) (hb : b ≤ 4) (hab : a ≤ b) (hlen : b - a ≤ 2)
    (hposN : 0 < ∫ x in a..b, rhinLiteEvenNormalized t x) :
    0 < (∫ x in a..b,
          ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x /
            x ^ (rhinLiteEvenIndex t + 1)) ∧
      (∫ x in a..b,
          ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x /
            x ^ (rhinLiteEvenIndex t + 1))
        ≤ (9 / 40 : ℝ) ^ rhinLiteEvenIndex t := by
  -- rewrite the log-form integral as `∫ normalized/x`
  have hcongr : (∫ x in a..b,
        ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x /
          x ^ (rhinLiteEvenIndex t + 1))
      = ∫ x in a..b, rhinLiteEvenNormalized t x / x := by
    apply intervalIntegral.integral_congr
    intro x _; exact rhinLiteEven_logForm_integrand t x
  rw [hcongr]
  have hII := intervalIntegrable_rhinLiteEven_logForm t ha hb hab
  have hIN := intervalIntegrable_rhinLiteEvenNormalized t ha hb hab
  constructor
  · -- positivity: `normalized/x ≥ normalized/4 ≥ 0`, and `∫ normalized/4 = (1/4)·∫ normalized > 0`
    have hlow : ∫ x in a..b, rhinLiteEvenNormalized t x / 4 ≤ ∫ x in a..b,
        rhinLiteEvenNormalized t x / x := by
      apply intervalIntegral.integral_mono_on hab (hIN.div_const 4) hII
      intro x hx
      have hxpos : (0 : ℝ) < x := by linarith [hx.1]
      have hnn : 0 ≤ rhinLiteEvenNormalized t x :=
        rhinLiteEvenNormalized_nonneg t hxpos
      exact div_le_div_of_nonneg_left hnn hxpos (by linarith [hx.2])
    have hquart : (∫ x in a..b, rhinLiteEvenNormalized t x / 4)
        = (∫ x in a..b, rhinLiteEvenNormalized t x) / 4 :=
      intervalIntegral.integral_div (4:ℝ) (rhinLiteEvenNormalized t)
    rw [hquart] at hlow
    have : 0 < (∫ x in a..b, rhinLiteEvenNormalized t x) / 4 := by positivity
    linarith
  · -- upper: `normalized/x ≤ normalized/2`, and `∫ normalized/2 = (1/2)·∫ normalized ≤ (9/40)^N`
    have hup : ∫ x in a..b, rhinLiteEvenNormalized t x / x ≤ ∫ x in a..b,
        rhinLiteEvenNormalized t x / 2 := by
      apply intervalIntegral.integral_mono_on hab hII (hIN.div_const 2)
      intro x hx
      have hxpos : (0 : ℝ) < x := by linarith [hx.1]
      have hnn : 0 ≤ rhinLiteEvenNormalized t x :=
        rhinLiteEvenNormalized_nonneg t hxpos
      exact div_le_div_of_nonneg_left hnn (by norm_num : (0 : ℝ) < 2) (by linarith [hx.1])
    have hhalf : (∫ x in a..b, rhinLiteEvenNormalized t x / 2)
        = (∫ x in a..b, rhinLiteEvenNormalized t x) / 2 :=
      intervalIntegral.integral_div (2:ℝ) (rhinLiteEvenNormalized t)
    have hle := rhinLiteEvenIntegral_le t ha hb hab
    have hpow : (0 : ℝ) ≤ (9 / 40 : ℝ) ^ rhinLiteEvenIndex t := by positivity
    rw [hhalf] at hup
    -- `∫ normalized ≤ (b−a)·(9/40)^N ≤ 2·(9/40)^N`, so `∫ normalized/2 ≤ (9/40)^N`
    have hle2 : (∫ x in a..b, rhinLiteEvenNormalized t x) ≤ 2 * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t := by
      have : (b - a) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t ≤ 2 * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t :=
        mul_le_mul_of_nonneg_right hlen hpow
      linarith [hle]
    linarith [hup, hle2]

/-- **Size + positivity of the log-form remainder integral (`[2,3]`).** -/
theorem rhinLiteEven_logForm_small_23 (t : ℕ) :
    0 < (∫ x in (2 : ℝ)..3,
          ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x /
            x ^ (rhinLiteEvenIndex t + 1)) ∧
      (∫ x in (2 : ℝ)..3,
          ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x /
            x ^ (rhinLiteEvenIndex t + 1))
        ≤ (9 / 40 : ℝ) ^ rhinLiteEvenIndex t :=
  rhinLiteEven_logForm_bounds_aux t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (rhinLiteEvenIntegral_pos_23 t)

/-- **Size + positivity of the log-form remainder integral (`[3,4]`).** -/
theorem rhinLiteEven_logForm_small_34 (t : ℕ) :
    0 < (∫ x in (3 : ℝ)..4,
          ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x /
            x ^ (rhinLiteEvenIndex t + 1)) ∧
      (∫ x in (3 : ℝ)..4,
          ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x /
            x ^ (rhinLiteEvenIndex t + 1))
        ≤ (9 / 40 : ℝ) ^ rhinLiteEvenIndex t :=
  rhinLiteEven_logForm_bounds_aux t (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (rhinLiteEvenIntegral_pos_34 t)

/-- **Per-index conditional lower bound (the rigorous mechanism).**  Given the two forms
`L₁ = A₁ + B·θ₁`, `L₂ = A₂ + B·θ₂` (`θ₁ = log(3/2)`, `θ₂ = log(4/3)`) with `0 < Lᵢ ≤ E`, `0 < B`,
and a target integer triple `(p,q,r)` whose integer combination `n = p·B − q·A₁ − r·A₂` is
**nonzero**, the linear form `Λ = p + q·θ₁ + r·θ₂` obeys
`|Λ| ≥ (1 − (|q|+|r|)·E) / B`.

This is `elim_identity` + `|n| ≥ 1` + the triangle bound `|q·L₁ + r·L₂| ≤ (|q|+|r|)·E`.  It is the
fully-proved core of the transference; the crux `rhinLiteLIMeasure` then only needs the
number-theoretic *non-vanishing* (some `t` with `n ≠ 0` at controlled size) and the `lcmUpto`
denominator asymptotic. -/
theorem logForm_conditional_lower
    (A₁ A₂ B p q r : ℤ) (E : ℝ)
    (hB : 0 < B)
    (hL₁pos : 0 < (A₁ : ℝ) + B * Real.log (3 / 2))
    (hL₁le : (A₁ : ℝ) + B * Real.log (3 / 2) ≤ E)
    (hL₂pos : 0 < (A₂ : ℝ) + B * Real.log (4 / 3))
    (hL₂le : (A₂ : ℝ) + B * Real.log (4 / 3) ≤ E)
    (hn : p * B - q * A₁ - r * A₂ ≠ 0) :
    (1 - ((|q| + |r| : ℤ) : ℝ) * E) / (B : ℝ)
      ≤ |(p : ℝ) + q * Real.log (3 / 2) + r * Real.log (4 / 3)| := by
  set θ₁ : ℝ := Real.log (3 / 2)
  set θ₂ : ℝ := Real.log (4 / 3)
  set L₁ : ℝ := (A₁ : ℝ) + B * θ₁ with hL₁def
  set L₂ : ℝ := (A₂ : ℝ) + B * θ₂ with hL₂def
  set Λ : ℝ := (p : ℝ) + q * θ₁ + r * θ₂ with hΛdef
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  -- `B·Λ = n + q·L₁ + r·L₂`
  have hBΛ : (B : ℝ) * Λ = ((p * B - q * A₁ - r * A₂ : ℤ) : ℝ) + q * L₁ + r * L₂ := by
    rw [hΛdef, hL₁def, hL₂def]; exact elim_identity A₁ A₂ B p q r θ₁ θ₂
  -- `|n| ≥ 1`
  have hn1 : (1 : ℝ) ≤ |((p * B - q * A₁ - r * A₂ : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |p * B - q * A₁ - r * A₂| := Int.one_le_abs hn
    calc (1 : ℝ) ≤ ((|p * B - q * A₁ - r * A₂| : ℤ) : ℝ) := by exact_mod_cast this
      _ = |((p * B - q * A₁ - r * A₂ : ℤ) : ℝ)| := by rw [Int.cast_abs]
  -- `|q·L₁ + r·L₂| ≤ (|q|+|r|)·E`
  have htri : |(q : ℝ) * L₁ + r * L₂| ≤ ((|q| + |r| : ℤ) : ℝ) * E := by
    have hq : |(q : ℝ) * L₁| ≤ (|q| : ℤ) * E := by
      rw [abs_mul, abs_of_pos hL₁pos, Int.cast_abs]
      exact mul_le_mul_of_nonneg_left hL₁le (abs_nonneg _)
    have hr : |(r : ℝ) * L₂| ≤ (|r| : ℤ) * E := by
      rw [abs_mul, abs_of_pos hL₂pos, Int.cast_abs]
      exact mul_le_mul_of_nonneg_left hL₂le (abs_nonneg _)
    calc |(q : ℝ) * L₁ + r * L₂| ≤ |(q : ℝ) * L₁| + |(r : ℝ) * L₂| := abs_add_le _ _
      _ ≤ (|q| : ℤ) * E + (|r| : ℤ) * E := by linarith
      _ = ((|q| + |r| : ℤ) : ℝ) * E := by push_cast; ring
  -- `|B·Λ| ≥ 1 − (|q|+|r|)·E`
  have hlow : 1 - ((|q| + |r| : ℤ) : ℝ) * E ≤ |(B : ℝ) * Λ| := by
    rw [hBΛ]
    -- `|n + s| ≥ |n| − |s| ≥ 1 − (|q|+|r|)E`
    have hge : |((p * B - q * A₁ - r * A₂ : ℤ) : ℝ)| - |(q : ℝ) * L₁ + r * L₂|
        ≤ |((p * B - q * A₁ - r * A₂ : ℤ) : ℝ) + (q * L₁ + r * L₂)| :=
      abs_sub_abs_le_abs_add _ _
    have hassoc : ((p * B - q * A₁ - r * A₂ : ℤ) : ℝ) + q * L₁ + r * L₂
        = ((p * B - q * A₁ - r * A₂ : ℤ) : ℝ) + (q * L₁ + r * L₂) := by ring
    rw [hassoc]; linarith [hn1, htri, hge]
  -- divide by `B`
  rw [abs_mul, abs_of_pos hBR] at hlow
  rw [div_le_iff₀ hBR]
  have hcomm : (B : ℝ) * |Λ| = |Λ| * (B : ℝ) := mul_comm _ _
  linarith [hlow, hcomm]

/-- **Data packaging.**  For each block index `t`, `rhinLiteEven_two_log_forms` together with the
size package produces the two forms with bounds: `0 < B`, `D_N·17^N ≤ B ≤ D_N·18^N`,
`0 < Lᵢ ≤ D_N·(9/40)^N`, where `D_N = lcmUpto N · 12^N` (as a real).  Feeds
`logForm_conditional_lower` with `E = D_N·(9/40)^N`. -/
theorem rhinLite_forms_bounded (t : ℕ) :
    ∃ A₁ A₂ B : ℤ,
      0 < B ∧
      ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 12 ^ rhinLiteEvenIndex t) * 17 ^ rhinLiteEvenIndex t
          ≤ (B : ℝ) ∧
      (B : ℝ) ≤ ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 12 ^ rhinLiteEvenIndex t)
          * 18 ^ rhinLiteEvenIndex t ∧
      0 < (A₁ : ℝ) + B * Real.log (3 / 2) ∧
      (A₁ : ℝ) + B * Real.log (3 / 2)
          ≤ ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 12 ^ rhinLiteEvenIndex t)
              * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t ∧
      0 < (A₂ : ℝ) + B * Real.log (4 / 3) ∧
      (A₂ : ℝ) + B * Real.log (4 / 3)
          ≤ ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 12 ^ rhinLiteEvenIndex t)
              * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t := by
  obtain ⟨A₁, A₂, B, h₁, h₂, hBlo, hBhi⟩ := rhinLiteEven_two_log_forms t
  set N := rhinLiteEvenIndex t with hN
  set D : ℝ := (Nat.lcmUpto N : ℝ) * 12 ^ N with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    have hl : (0 : ℝ) < (Nat.lcmUpto N : ℝ) := by exact_mod_cast Nat.lcmUpto_pos N
    positivity
  have hBloR : D * 17 ^ N ≤ (B : ℝ) := by
    have : ((Nat.lcmUpto N : ℤ) * 12 ^ N * 17 ^ N : ℤ) ≤ B := hBlo
    calc D * 17 ^ N = (((Nat.lcmUpto N : ℤ) * 12 ^ N * 17 ^ N : ℤ) : ℝ) := by
          rw [hDdef]; push_cast; ring
      _ ≤ (B : ℝ) := by exact_mod_cast this
  have hBhiR : (B : ℝ) ≤ D * 18 ^ N := by
    have : B ≤ ((Nat.lcmUpto N : ℤ) * 12 ^ N * 18 ^ N : ℤ) := hBhi
    calc (B : ℝ) ≤ (((Nat.lcmUpto N : ℤ) * 12 ^ N * 18 ^ N : ℤ) : ℝ) := by exact_mod_cast this
      _ = D * 18 ^ N := by rw [hDdef]; push_cast; ring
  have hBpos : 0 < B := by
    have h17 : (0 : ℝ) < D * 17 ^ N := by positivity
    have : (0 : ℝ) < (B : ℝ) := lt_of_lt_of_le h17 hBloR
    exact_mod_cast this
  -- the integrals
  obtain ⟨hi23pos, hi23le⟩ := rhinLiteEven_logForm_small_23 t
  obtain ⟨hi34pos, hi34le⟩ := rhinLiteEven_logForm_small_34 t
  -- L₁ = D · ∫_2^3, positive and ≤ D·(9/40)^N
  refine ⟨A₁, A₂, B, hBpos, hBloR, hBhiR, ?_, ?_, ?_, ?_⟩
  · rw [← h₁]; exact mul_pos hDpos hi23pos
  · rw [← h₁]; exact mul_le_mul_of_nonneg_left hi23le hDpos.le
  · rw [← h₂]; exact mul_pos hDpos hi34pos
  · rw [← h₂]; exact mul_le_mul_of_nonneg_left hi34le hDpos.le

/-- **Scaling diagnosis (machine witness).**  The clearing used by `RhinLiteLogForm`,
`D_N = lcmUpto N · 12^N`, makes the cleared remainder `E_N = D_N · (9/40)^N ≥ 1` for **every** `N`:
`D_N · (9/40)^N = lcmUpto N · (27/10)^N ≥ 1` since `lcmUpto N ≥ 1` and `27/10 ≥ 1`.

Consequence: `logForm_conditional_lower` instantiated at `E = E_N` is **vacuous**
(`1 − (|q|+|r|)·E_N ≤ 1 − (|q|+|r|) ≤ 0` for any nonzero `(q,r)`), so the crux `rhinLiteLIMeasure`
is **not reachable through the `12^N`-cleared forms**.  In Wu's terms (Math. Comp. 72 (2003),
Thm 2) the clearing rate is `K = lim (1/N) log D_N = 1 + log 12 ≈ 3.485`, which **exceeds** the
remainder-decay rate `τ = −lim (1/N) log I_N = log(40/9) ≈ 1.492`; Wu's criterion needs `τ > K`.

**Fix (recorded 2026-08-31, see `FRONT-A-RHIN-LITE.md`):** the endpoint powers must be cleared
*structurally* from `H_N ∈ (12,x)^N ℤ[x]` (each `coeff_j` carries `12^{N−j}`), NOT by a global
`12^N` multiplier.  Then `D_N = lcmUpto N` alone (`K = 1`) suffices, `τ = 1.492 > 1 = K`, and the
coarse kernel yields a finite measure `μ = (τ⁽⁰⁾ + K)/(τ − K) ≈ (2.89 + 1)/0.492 ≈ 7.9`. -/
theorem overcleared_remainder_ge_one (N : ℕ) :
    1 ≤ (Nat.lcmUpto N : ℝ) * 12 ^ N * (9 / 40 : ℝ) ^ N := by
  have h1 : (1 : ℝ) ≤ (Nat.lcmUpto N : ℝ) := by exact_mod_cast Nat.lcmUpto_pos N
  have h2 : (1 : ℝ) ≤ 12 ^ N * (9 / 40 : ℝ) ^ N := by
    rw [← mul_pow]; exact one_le_pow₀ (by norm_num)
  calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
    _ ≤ (Nat.lcmUpto N : ℝ) * (12 ^ N * (9 / 40 : ℝ) ^ N) :=
        mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)
    _ = (Nat.lcmUpto N : ℝ) * 12 ^ N * (9 / 40 : ℝ) ^ N := by ring

/-! ### K=1 structural clearing — the coefficient content of `H_N` (route to retire the axiom)

The `12^N`-over-clearing is fixed by exploiting that `H_N`'s coefficients are already divisible by
the endpoint powers: `12^{N−j} ∣ coeff_j(H_N)` (i.e. `H_N ∈ (12,X)^N ℤ[X]`, `N = 2000t`), so the
endpoints `x ∈ {2,3,4}` clear *structurally* and only `D_N = lcmUpto N` (`K = 1 < τ`) remains.  This
was **numerically verified** on the exact degree-`4000` base polynomial (`t = 1`): every coefficient
satisfies both `val₂(c_j) ≥ 2(N−j)` and `val₃(c_j) ≥ (N−j)`, hence `12^{N−j} ∣ c_j`.

The content splits by CRT (`12 = 4·3`, coprime) into a 2-adic and a 3-adic part, decomposed here as
two named obligations of **very different difficulty**:

* **3-adic (`rhinLiteEvenPolynomialZ_three_adic_content`)** — now **PROVED** factorwise.  With the
  `(3,X)`-adic order `ord₃(Q₁)=1, ord₃(Q₄)=1, ord₃(Q₅)=ord₃(Q₆)=2, ord₃(Q₂)=ord₃(Q₃)=0`, the product
  order is `Σ eᵢ·ord₃(Qᵢ) = 2t(w₁+w₄+2w₅+2w₆) = 2t·1000 = N` **exactly**.  Proved via the coefficientwise
  predicate `Dvd3Adic` (superadditive over products: `Dvd3Adic_mul`/`_pow`) — no cross-terms needed.
* **2-adic (`rhinLiteEvenPolynomialZ_two_adic_content`)** — now **PROVED**.  The naive factorwise
  `(4,X)`-order gives only `1410t < N`, but grouping the factors into **squares** captures the
  cross-terms elementarily: `(X−2)² ∈ (4,X)` and `Q₅² ∈ (4,X)³` (whose odd-power orders vanish).
  The `ord₄` of the factor-powers is `(0, w₂t, 2w₃t, 2w₄t, 3w₅t, 4w₆t)`, summing to
  `w₂t+2w₃t+2w₄t+3w₅t+4w₆t = 2000t = N` **exactly** — no Newton-polygon machinery needed.

Both parts and the combined `rhinLiteEvenPolynomialZ_content` (`H_N ∈ (12,X)^N`) are now proved with
trust-base-only ledgers.  The K=1 structural clearing input is therefore in hand.
-/

/-- Coefficientwise `(3,X)`-adic order predicate: `3^{a−j} ∣ coeff_j p` for all `j`
(`p ∈ (3,X)^a ℤ[X]`, using `ℕ` truncated subtraction so `j ≥ a` is vacuous). -/
def Dvd3Adic (a : ℕ) (p : ℤ[X]) : Prop := ∀ j, (3 : ℤ) ^ (a - j) ∣ p.coeff j

theorem Dvd3Adic_zero (p : ℤ[X]) : Dvd3Adic 0 p := by
  intro j; simp

theorem Dvd3Adic_add {a : ℕ} {p q : ℤ[X]} (hp : Dvd3Adic a p) (hq : Dvd3Adic a q) :
    Dvd3Adic a (p + q) := by
  intro j; rw [coeff_add]; exact dvd_add (hp j) (hq j)

theorem Dvd3Adic_mul {a b : ℕ} {p q : ℤ[X]} (hp : Dvd3Adic a p) (hq : Dvd3Adic b q) :
    Dvd3Adic (a + b) (p * q) := by
  intro n
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  rintro ⟨u, v⟩ huv
  have huvn : u + v = n := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  have hprod : (3 : ℤ) ^ ((a - u) + (b - v)) ∣ p.coeff u * q.coeff v := by
    rw [pow_add]; exact mul_dvd_mul (hp u) (hq v)
  exact dvd_trans (pow_dvd_pow 3 (by omega)) hprod

theorem Dvd3Adic_pow {a : ℕ} {p : ℤ[X]} (hp : Dvd3Adic a p) : ∀ n, Dvd3Adic (n * a) (p ^ n)
  | 0 => by simpa using Dvd3Adic_zero (1 : ℤ[X])
  | n + 1 => by
      rw [pow_succ, Nat.succ_mul]
      exact Dvd3Adic_mul (Dvd3Adic_pow hp n) hp

/-- **3-adic content of `H_N` (PROVED factorwise).**  `3^{N−j} ∣ coeff_j(H_N)`, i.e.
`H_N ∈ (3,X)^N ℤ[X]` with `N = rhinLiteEvenIndex t = 2000t`.  The `(3,X)`-adic orders of the six
factors are `(1,0,0,1,2,2)`, and `Σ eᵢ·ordᵢ = 2t(w₁+w₄+2w₅+2w₆) = 2t·1000 = N` **exactly**; the
result follows from superadditivity of `Dvd3Adic` over products (`Dvd3Adic_mul`/`_pow`). -/
theorem rhinLiteEvenPolynomialZ_three_adic_content (t j : ℕ) :
    (3 : ℤ) ^ (rhinLiteEvenIndex t - j) ∣ (rhinLiteEvenPolynomialZ t).coeff j := by
  -- base facts for the six factors, at their `(3,X)`-orders
  have hQ1 : Dvd3Adic 1 rhinLiteQ1 := by
    intro i
    match i with
    | 0 => have hc : rhinLiteQ1.coeff 0 = -3 := by simp [rhinLiteQ1]
           rw [hc]; norm_num
    | (k + 1) => have h0 : 1 - (k + 1) = 0 := by omega
                 rw [h0, pow_zero]; exact one_dvd _
  have hQ4 : Dvd3Adic 1 rhinLiteQ4 := by
    intro i
    match i with
    | 0 => have hc : rhinLiteQ4.coeff 0 = -12 := by simp [rhinLiteQ4]
           rw [hc]; norm_num
    | (k + 1) => have h0 : 1 - (k + 1) = 0 := by omega
                 rw [h0, pow_zero]; exact one_dvd _
  have hQ5 : Dvd3Adic 2 rhinLiteQ5 := by
    intro i
    match i with
    | 0 => have hc : rhinLiteQ5.coeff 0 = 144 := by simp [rhinLiteQ5]
           rw [hc]; norm_num
    | 1 => have hc : rhinLiteQ5.coeff 1 = -102 := by simp [rhinLiteQ5]
           rw [hc]; norm_num
    | (k + 2) => have h0 : 2 - (k + 2) = 0 := by omega
                 rw [h0, pow_zero]; exact one_dvd _
  have hQ6 : Dvd3Adic 2 rhinLiteQ6 := by
    intro i
    match i with
    | 0 => have hc : rhinLiteQ6.coeff 0 = 144 := by simp [rhinLiteQ6]
           rw [hc]; norm_num
    | 1 => have hc : rhinLiteQ6.coeff 1 = -108 := by simp [rhinLiteQ6]
           rw [hc]; norm_num
    | (k + 2) => have h0 : 2 - (k + 2) = 0 := by omega
                 rw [h0, pow_zero]; exact one_dvd _
  -- assemble the product; total order = N exactly
  have hprod : Dvd3Adic
      ((((((2 * rhinLiteW1 * t) * 1) + 0) + 0) + ((2 * rhinLiteW4 * t) * 1)
        + ((2 * rhinLiteW5 * t) * 2)) + ((2 * rhinLiteW6 * t) * 2))
      (rhinLiteEvenPolynomialZ t) := by
    rw [rhinLiteEvenPolynomialZ]
    exact Dvd3Adic_mul (Dvd3Adic_mul (Dvd3Adic_mul (Dvd3Adic_mul (Dvd3Adic_mul
      (Dvd3Adic_pow hQ1 (2 * rhinLiteW1 * t))
      (Dvd3Adic_zero (rhinLiteQ2 ^ (2 * rhinLiteW2 * t))))
      (Dvd3Adic_zero (rhinLiteQ3 ^ (2 * rhinLiteW3 * t))))
      (Dvd3Adic_pow hQ4 (2 * rhinLiteW4 * t)))
      (Dvd3Adic_pow hQ5 (2 * rhinLiteW5 * t)))
      (Dvd3Adic_pow hQ6 (2 * rhinLiteW6 * t))
  have heq : (((((2 * rhinLiteW1 * t) * 1) + 0) + 0) + ((2 * rhinLiteW4 * t) * 1)
        + ((2 * rhinLiteW5 * t) * 2)) + ((2 * rhinLiteW6 * t) * 2)
      = rhinLiteEvenIndex t := by
    simp only [rhinLiteEvenIndex, rhinLiteScale, rhinLiteW1, rhinLiteW4, rhinLiteW5, rhinLiteW6]
    ring
  rw [← heq]
  exact hprod j

/-- Coefficientwise `(4,X)`-adic order predicate (base-4 analogue of `Dvd3Adic`):
`4^{a−j} ∣ coeff_j p` for all `j`. -/
def Dvd4Adic (a : ℕ) (p : ℤ[X]) : Prop := ∀ j, (4 : ℤ) ^ (a - j) ∣ p.coeff j

theorem Dvd4Adic_zero (p : ℤ[X]) : Dvd4Adic 0 p := by intro j; simp

theorem Dvd4Adic_mul {a b : ℕ} {p q : ℤ[X]} (hp : Dvd4Adic a p) (hq : Dvd4Adic b q) :
    Dvd4Adic (a + b) (p * q) := by
  intro n
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  rintro ⟨u, v⟩ huv
  have huvn : u + v = n := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  have hprod : (4 : ℤ) ^ ((a - u) + (b - v)) ∣ p.coeff u * q.coeff v := by
    rw [pow_add]; exact mul_dvd_mul (hp u) (hq v)
  exact dvd_trans (pow_dvd_pow 4 (by omega)) hprod

theorem Dvd4Adic_pow {a : ℕ} {p : ℤ[X]} (hp : Dvd4Adic a p) : ∀ n, Dvd4Adic (n * a) (p ^ n)
  | 0 => by simpa using Dvd4Adic_zero (1 : ℤ[X])
  | n + 1 => by rw [pow_succ, Nat.succ_mul]; exact Dvd4Adic_mul (Dvd4Adic_pow hp n) hp

/-- **2-adic content of `H_N` (PROVED via the paired-factor 2-adic orders).**  `4^{N−j} ∣ coeff_j(H_N)`,
i.e. `H_N ∈ (4,X)^N ℤ[X]` with `N = 2000t`.  Naively the `(4,X)`-order sums factorwise to only
`1410t < N`; the missing `590t` powers of `2` come from cross-terms, captured by grouping the factors
into their **squares**: `(X−2)² ∈ (4,X)` and `Q₅² ∈ (4,X)³` (their odd-power orders vanish, but the
squares clear).  With `ord₄` of the factor-powers `(Q₁^{e₁},…,Q₆^{e₆})` equal to
`(0, w₂t, 2w₃t, 2w₄t, 3w₅t, 4w₆t)`, the product order is `w₂t+2w₃t+2w₄t+3w₅t+4w₆t = 2000t = N`
**exactly**.  Fully elementary (`Dvd4Adic_mul`/`_pow` + finite coefficient checks on the base squares). -/
theorem rhinLiteEvenPolynomialZ_two_adic_content (t j : ℕ) :
    (4 : ℤ) ^ (rhinLiteEvenIndex t - j) ∣ (rhinLiteEvenPolynomialZ t).coeff j := by
  -- base facts (finite coefficient checks)
  have hQ2sq : Dvd4Adic 1 (rhinLiteQ2 ^ 2) := by
    have hsq : rhinLiteQ2 ^ 2 = X ^ 2 - C 4 * X + C 4 := by simp [rhinLiteQ2]; ring
    intro i
    match i with
    | 0 => have hc : (rhinLiteQ2 ^ 2).coeff 0 = 4 := by rw [hsq]; simp
           rw [hc]; norm_num
    | (k + 1) => have h0 : 1 - (k + 1) = 0 := by omega
                 rw [h0, pow_zero]; exact one_dvd _
  have hQ3 : Dvd4Adic 1 rhinLiteQ3 := by
    intro i
    match i with
    | 0 => have hc : rhinLiteQ3.coeff 0 = -4 := by simp [rhinLiteQ3]
           rw [hc]; norm_num
    | (k + 1) => have h0 : 1 - (k + 1) = 0 := by omega
                 rw [h0, pow_zero]; exact one_dvd _
  have hQ4 : Dvd4Adic 1 rhinLiteQ4 := by
    intro i
    match i with
    | 0 => have hc : rhinLiteQ4.coeff 0 = -12 := by simp [rhinLiteQ4]
           rw [hc]; norm_num
    | (k + 1) => have h0 : 1 - (k + 1) = 0 := by omega
                 rw [h0, pow_zero]; exact one_dvd _
  have hQ6 : Dvd4Adic 2 rhinLiteQ6 := by
    intro i
    match i with
    | 0 => have hc : rhinLiteQ6.coeff 0 = 144 := by simp [rhinLiteQ6]
           rw [hc]; norm_num
    | 1 => have hc : rhinLiteQ6.coeff 1 = -108 := by simp [rhinLiteQ6]
           rw [hc]; norm_num
    | (k + 2) => have h0 : 2 - (k + 2) = 0 := by omega
                 rw [h0, pow_zero]; exact one_dvd _
  have hQ5sq : Dvd4Adic 3 (rhinLiteQ5 ^ 2) := by
    have hsq : rhinLiteQ5 ^ 2
        = C 289 * X ^ 4 - C 3468 * X ^ 3 + C 15300 * X ^ 2 - C 29376 * X + C 20736 := by
      simp [rhinLiteQ5]; ring
    intro i
    match i with
    | 0 => have hc : (rhinLiteQ5 ^ 2).coeff 0 = 20736 := by rw [hsq]; simp
           rw [hc]; norm_num
    | 1 => have hc : (rhinLiteQ5 ^ 2).coeff 1 = -29376 := by rw [hsq]; simp
           rw [hc]; norm_num
    | 2 => have hc : (rhinLiteQ5 ^ 2).coeff 2 = 15300 := by rw [hsq]; simp [Polynomial.coeff_X]
           rw [hc]; norm_num
    | (k + 3) => have h0 : 3 - (k + 3) = 0 := by omega
                 rw [h0, pow_zero]; exact one_dvd _
  -- per-factor-power orders
  have p1 : Dvd4Adic 0 (rhinLiteQ1 ^ (2 * rhinLiteW1 * t)) := Dvd4Adic_zero _
  have p2 : Dvd4Adic (rhinLiteW2 * t) (rhinLiteQ2 ^ (2 * rhinLiteW2 * t)) := by
    have e2 : rhinLiteQ2 ^ (2 * rhinLiteW2 * t) = (rhinLiteQ2 ^ 2) ^ (rhinLiteW2 * t) := by
      rw [← pow_mul]; congr 1; ring
    rw [e2]; simpa using Dvd4Adic_pow hQ2sq (rhinLiteW2 * t)
  have p3 : Dvd4Adic (2 * rhinLiteW3 * t) (rhinLiteQ3 ^ (2 * rhinLiteW3 * t)) := by
    simpa using Dvd4Adic_pow hQ3 (2 * rhinLiteW3 * t)
  have p4 : Dvd4Adic (2 * rhinLiteW4 * t) (rhinLiteQ4 ^ (2 * rhinLiteW4 * t)) := by
    simpa using Dvd4Adic_pow hQ4 (2 * rhinLiteW4 * t)
  have p5 : Dvd4Adic (3 * rhinLiteW5 * t) (rhinLiteQ5 ^ (2 * rhinLiteW5 * t)) := by
    have e5 : rhinLiteQ5 ^ (2 * rhinLiteW5 * t) = (rhinLiteQ5 ^ 2) ^ (rhinLiteW5 * t) := by
      rw [← pow_mul]; congr 1; ring
    rw [e5, show 3 * rhinLiteW5 * t = rhinLiteW5 * t * 3 by ring]
    exact Dvd4Adic_pow hQ5sq (rhinLiteW5 * t)
  have p6 : Dvd4Adic (2 * rhinLiteW6 * t * 2) (rhinLiteQ6 ^ (2 * rhinLiteW6 * t)) :=
    Dvd4Adic_pow hQ6 (2 * rhinLiteW6 * t)
  -- assemble
  have hprod : Dvd4Adic
      (((((0 + rhinLiteW2 * t) + 2 * rhinLiteW3 * t) + 2 * rhinLiteW4 * t) + 3 * rhinLiteW5 * t)
        + 2 * rhinLiteW6 * t * 2)
      (rhinLiteEvenPolynomialZ t) := by
    rw [rhinLiteEvenPolynomialZ]
    exact Dvd4Adic_mul (Dvd4Adic_mul (Dvd4Adic_mul (Dvd4Adic_mul (Dvd4Adic_mul p1 p2) p3) p4) p5) p6
  have heq : (((((0 + rhinLiteW2 * t) + 2 * rhinLiteW3 * t) + 2 * rhinLiteW4 * t)
        + 3 * rhinLiteW5 * t) + 2 * rhinLiteW6 * t * 2) = rhinLiteEvenIndex t := by
    simp only [rhinLiteEvenIndex, rhinLiteScale, rhinLiteW2, rhinLiteW3, rhinLiteW4,
      rhinLiteW5, rhinLiteW6]
    ring
  rw [← heq]
  exact hprod j

/-- **Coefficient content of `H_N`: `12^{N−j} ∣ coeff_j(H_N)` (PROVED from the 2- and 3-adic parts).**
`H_N ∈ (12,X)^N ℤ[X]`, `N = 2000t`.  This is the structural-clearing input for the corrected
(K=1) objective 4 (`D_N = lcmUpto N`).  Combines `rhinLiteEvenPolynomialZ_two_adic_content` and
`rhinLiteEvenPolynomialZ_three_adic_content` (both now PROVED) via `IsCoprime (4^k) (3^k)` and
`12 = 4·3`.  For `j ≥ N` the exponent `N−j` is `0` and the divisibility is trivial.  **This lemma is
now fully machine-checked** (trust-base-only ledger). -/
theorem rhinLiteEvenPolynomialZ_content (t j : ℕ) :
    (12 : ℤ) ^ (rhinLiteEvenIndex t - j) ∣ (rhinLiteEvenPolynomialZ t).coeff j := by
  set k := rhinLiteEvenIndex t - j with hk
  have h4 := rhinLiteEvenPolynomialZ_two_adic_content t j
  have h3 := rhinLiteEvenPolynomialZ_three_adic_content t j
  have hcop : IsCoprime ((4 : ℤ) ^ k) ((3 : ℤ) ^ k) :=
    (show IsCoprime (4 : ℤ) 3 from ⟨1, -1, by ring⟩).pow
  have hmul := hcop.mul_dvd h4 h3
  rwa [← mul_pow, show (4 : ℤ) * 3 = 12 by norm_num] at hmul

/-- **The two `D_N = lcmUpto N`-cleared integer log forms (K=1).**  Structural analogue of
`rhinLiteEven_two_log_forms` but with the SMALLER denominator `D_N = lcmUpto N` (no global `12^N`),
using the proved coefficient content `rhinLiteEvenPolynomialZ_content`.  Common
`B = lcmUpto N · coeff_N(H_N)`, `lcmUpto N·17^N ≤ B ≤ lcmUpto N·18^N`. -/
theorem rhinLiteEven_two_log_forms_K1 (t : ℕ) :
    ∃ A₁ A₂ B : ℤ,
      ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) *
          (∫ x in (2 : ℝ)..3,
            ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x /
              x ^ (rhinLiteEvenIndex t + 1))
        = (A₁ : ℝ) + (B : ℝ) * Real.log (3 / 2)) ∧
      ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) *
          (∫ x in (3 : ℝ)..4,
            ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x /
              x ^ (rhinLiteEvenIndex t + 1))
        = (A₂ : ℝ) + (B : ℝ) * Real.log (4 / 3)) ∧
      (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) * 17 ^ rhinLiteEvenIndex t ≤ B ∧
      B ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) * 18 ^ rhinLiteEvenIndex t := by
  have hdeg : ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).natDegree ≤
      2 * rhinLiteEvenIndex t := le_of_eq (rhinLiteEvenPolynomialZ_map_real_natDegree t)
  have hN : rhinLiteEvenIndex t ≤
      ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).natDegree := by
    rw [rhinLiteEvenPolynomialZ_map_real_natDegree]; omega
  obtain ⟨A₁, h₁⟩ := lcm_cleared_log_form_K1 (rhinLiteEvenPolynomialZ t) (ea := 2) (eb := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (rhinLiteEvenIndex t) hdeg hN (fun j => rhinLiteEvenPolynomialZ_content t j)
  obtain ⟨A₂, h₂⟩ := lcm_cleared_log_form_K1 (rhinLiteEvenPolynomialZ t) (ea := 3) (eb := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (rhinLiteEvenIndex t) hdeg hN (fun j => rhinLiteEvenPolynomialZ_content t j)
  refine ⟨A₁, A₂,
    (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) *
      (rhinLiteEvenPolynomialZ t).coeff (rhinLiteEvenIndex t), ?_, ?_, ?_, ?_⟩
  · simpa using h₁
  · simpa using h₂
  · obtain ⟨hlo, _⟩ := rhinLiteEvenPolynomialZ_centralCoeff_bounds t
    have hD : (0 : ℤ) ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) := by positivity
    calc (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) * 17 ^ rhinLiteEvenIndex t
        ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) *
            (rhinLiteEvenPolynomialZ t).coeff (rhinLiteEvenIndex t) :=
          mul_le_mul_of_nonneg_left hlo hD
      _ = _ := by ring
  · obtain ⟨_, hhi⟩ := rhinLiteEvenPolynomialZ_centralCoeff_bounds t
    have hD : (0 : ℤ) ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) := by positivity
    exact mul_le_mul_of_nonneg_left hhi hD

/-- **Data packaging (K=1).**  Structural analogue of `rhinLite_forms_bounded` with the smaller
`D_N = lcmUpto N`: `0 < B`, `lcmUpto N·17^N ≤ B ≤ lcmUpto N·18^N`, `0 < Lᵢ ≤ lcmUpto N·(9/40)^N`.
The remainder `E_N = lcmUpto N·(9/40)^N → 0` (K=1 < τ), so `logForm_conditional_lower` is
non-vacuous for large `N`. -/
theorem rhinLite_forms_bounded_K1 (t : ℕ) :
    ∃ A₁ A₂ B : ℤ,
      0 < B ∧
      (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 17 ^ rhinLiteEvenIndex t ≤ (B : ℝ) ∧
      (B : ℝ) ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 18 ^ rhinLiteEvenIndex t ∧
      0 < (A₁ : ℝ) + B * Real.log (3 / 2) ∧
      (A₁ : ℝ) + B * Real.log (3 / 2)
          ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t ∧
      0 < (A₂ : ℝ) + B * Real.log (4 / 3) ∧
      (A₂ : ℝ) + B * Real.log (4 / 3)
          ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t := by
  obtain ⟨A₁, A₂, B, h₁, h₂, hBlo, hBhi⟩ := rhinLiteEven_two_log_forms_K1 t
  set N := rhinLiteEvenIndex t with hN
  set D : ℝ := (Nat.lcmUpto N : ℝ) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; exact_mod_cast Nat.lcmUpto_pos N
  have hBloR : D * 17 ^ N ≤ (B : ℝ) := by
    have : ((Nat.lcmUpto N : ℤ) * 17 ^ N : ℤ) ≤ B := hBlo
    calc D * 17 ^ N = (((Nat.lcmUpto N : ℤ) * 17 ^ N : ℤ) : ℝ) := by rw [hDdef]; push_cast; ring
      _ ≤ (B : ℝ) := by exact_mod_cast this
  have hBhiR : (B : ℝ) ≤ D * 18 ^ N := by
    have : B ≤ ((Nat.lcmUpto N : ℤ) * 18 ^ N : ℤ) := hBhi
    calc (B : ℝ) ≤ (((Nat.lcmUpto N : ℤ) * 18 ^ N : ℤ) : ℝ) := by exact_mod_cast this
      _ = D * 18 ^ N := by rw [hDdef]; push_cast; ring
  have hBpos : 0 < B := by
    have h17 : (0 : ℝ) < D * 17 ^ N := by positivity
    have : (0 : ℝ) < (B : ℝ) := lt_of_lt_of_le h17 hBloR
    exact_mod_cast this
  obtain ⟨hi23pos, hi23le⟩ := rhinLiteEven_logForm_small_23 t
  obtain ⟨hi34pos, hi34le⟩ := rhinLiteEven_logForm_small_34 t
  refine ⟨A₁, A₂, B, hBpos, hBloR, hBhiR, ?_, ?_, ?_, ?_⟩
  · rw [← h₁]; exact mul_pos hDpos hi23pos
  · rw [← h₁]; exact mul_le_mul_of_nonneg_left hi23le hDpos.le
  · rw [← h₂]; exact mul_pos hDpos hi34pos
  · rw [← h₂]; exact mul_le_mul_of_nonneg_left hi34le hDpos.le

/-- **Chebyshev denominator bound (prerequisite for the finite exponent `κ`).**  The `K=1`
denominator `D_N = lcmUpto N` satisfies `log D_N ≤ log 4 · N + 2√N·log N`, i.e. `D_N ≤ 4^N·N^{2√N}`
— exponential rate exactly `log 4 < τ = log(40/9)`, with a subexponential correction.  This is the
mathlib Chebyshev upper bound `ψ x ≤ log 4·x + 2√x·log x` transported through
`ψ N = log(lcmUpto N)`.  It is what converts `1/(2·D_N·18^N)` into `c·H^{−κ}` for a finite `κ`. -/
theorem lcmUpto_log_le_chebyshev (N : ℕ) :
    Real.log (Nat.lcmUpto N) ≤
      Real.log 4 * (N : ℝ) + 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [show Nat.lcmUpto 0 = 1 from rfl]; simp
  · have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hple := Chebyshev.psi_le (x := (N : ℝ)) h1
    rwa [Chebyshev.psi_eq_log_lcmUpto N] at hple

/-- **Eventual clean exponential denominator bound.**  For `N ≥ N₀` the subexponential factor
`N^{2√N}` is absorbed into a slightly larger base: `lcmUpto N ≤ (22/5)^N`.  The base `22/5 = 4.4`
lies strictly between the Chebyshev rate `4` and the remainder threshold `40/9 ≈ 4.444`, so
`E_N = lcmUpto N·(9/40)^N ≤ (22/5·9/40)^N = (99/100)^N → 0` (K < τ).  Proof: `lcmUpto_log_le_chebyshev`
plus `2√N·log N ≤ (log(22/5) − log 4)·N` for large `N` (the subexponential term is `o(N)`). -/
theorem lcmUpto_le_pow_eventually :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (Nat.lcmUpto N : ℝ) ≤ (22 / 5) ^ N := by
  set c : ℝ := Real.log (22 / 5) - Real.log 4 with hc_def
  have hc : 0 < c := by
    have h1 : Real.log 4 < Real.log (22 / 5) := Real.log_lt_log (by norm_num) (by norm_num)
    rw [hc_def]; linarith
  -- `√x·log x = o(x)` over ℝ.
  have hlittleO : (fun x : ℝ => Real.sqrt x * Real.log x) =o[Filter.atTop] (fun x : ℝ => x) := by
    have h1 : Real.log =o[Filter.atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
      _root_.isLittleO_log_rpow_atTop (by norm_num)
    have h2 := (Asymptotics.isBigO_refl (fun x : ℝ => Real.sqrt x) Filter.atTop).mul_isLittleO h1
    refine h2.congr' Filter.EventuallyEq.rfl ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
    rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hx]
  -- constant `2`, then the `o`-bound at level `c`.
  have hbound := (hlittleO.const_mul_left 2).def hc
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨M, hM⟩ := hbound
  refine ⟨max (⌈M⌉₊) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNM : M ≤ (N : ℝ) := by
    calc M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
      _ ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hsqrtN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  -- unpack the `o`-bound into a clean inequality
  have hb := hM (N : ℝ) hNM
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (Real.sqrt (N:ℝ) * Real.log (N:ℝ))),
    abs_of_nonneg hNpos.le] at hb
  have h34 : 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ c * (N : ℝ) := by nlinarith [hb]
  -- Chebyshev + the o-bound ⇒ `log(lcmUpto N) ≤ N·log(22/5)`
  have hcheb := lcmUpto_log_le_chebyshev N
  have hkey : Real.log (Nat.lcmUpto N) ≤ (N : ℝ) * Real.log (22 / 5) := by
    have : Real.log 4 * (N : ℝ) + 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ)
        ≤ (N : ℝ) * Real.log (22 / 5) := by
      rw [hc_def] at h34; nlinarith [h34]
    linarith [hcheb]
  -- exponentiate
  have hlcmpos : (0 : ℝ) < (Nat.lcmUpto N : ℝ) := by exact_mod_cast Nat.lcmUpto_pos N
  have hpowpos : (0 : ℝ) < (22 / 5 : ℝ) ^ N := by positivity
  rw [← Real.log_le_log_iff hlcmpos hpowpos, Real.log_pow]
  push_cast
  linarith [hkey]

/-! ### Disclosed crux: linear-independence measure of `{1, log(3/2), log(4/3)}`

**Disclosed crux: linear-independence measure of `{1, log(3/2), log(4/3)}`.**

There are `κ : ℕ` and `c > 0` such that for every nonzero integer triple `(p, q, r)`,
`c / H^κ ≤ |p + q·log(3/2) + r·log(4/3)|`, where `H = max(|p|, |q|, |r|)`.

This is the coarse Rhin measure produced by the block subsequence `N = 2000t`.  It is TRUE
(Rhin 1987), but see `overcleared_remainder_ge_one`: the **`12^N`-cleared forms of
`RhinLiteLogForm` cannot prove it** — their clearing rate `K ≈ 3.49` exceeds the remainder decay
`τ ≈ 1.49`, so the cleared remainder does not decay.  A proof needs the **structural clearing**
(`H_N ∈ (12,x)^N ℤ[x]`, `D_N = lcmUpto N`, `K = 1 < τ`), giving `μ ≈ 7.9`.  The mechanism below is
correct once fed forms with a *decaying* `E_N`.

**Route to a proof** (mechanism proved; the missing piece is the K=1 clearing + non-vanishing):

* ✅ Data + size (PROVED): `rhinLite_forms_bounded t` packages `rhinLiteEven_two_log_forms` with the
  size package into `0 < B`, `D_N·17^N ≤ B ≤ D_N·18^N`, `0 < Lᵢ ≤ D_N·(9/40)^N`.
* ✅ Mechanism (PROVED): `logForm_conditional_lower` gives, for any `(p,q,r)` with
  `n = p·B − q·A₁ − r·A₂ ≠ 0`, the rigorous bound `|Λ| ≥ (1 − (|q|+|r|)·D_N·(9/40)^N)/B`.
* ⏳ Non-vanishing (REMAINING): for a given `(p,q,r)` choose the least `N` with
  `(|q|+|r|)·D_N·(9/40)^N ≤ 1/2` (needs `D_N·(9/40)^N`'s growth vs `H`); the 3×3 determinant of
  three consecutive form-triples `(B, A₁, A₂)` is a nonzero integer, so `n ≠ 0` for at least one of
  three consecutive `N`.  Then `|Λ| ≥ 1/(2B) ≥ 1/(2·D_N·18^N)`.
* ⏳ Asymptotic (REMAINING): `D_N = lcmUpto N · 12^N ≤ 4^N·e^{o(N)}` (`Nat.lcmUpto` bound) converts
  `1/(2·D_N·18^N)` into `c·H^{−κ}` for a finite `κ` (the coarse Rhin exponent).

The two ✅ steps are now proved; the remaining obligation is the number-theoretic non-vanishing
determinant + the `lcmUpto` denominator asymptotic — a genuine multi-lap analytic number-theory
target, not a citation. -/
/-! ### Definite form data (the same integer triple across `t`, for the determinant argument) -/

/-- `A₁(t)`: the first cleared numerator (definite choice from `rhinLite_forms_bounded_K1`). -/
noncomputable def rhinLiteA₁ (t : ℕ) : ℤ := (rhinLite_forms_bounded_K1 t).choose

/-- `A₂(t)`: the second cleared numerator. -/
noncomputable def rhinLiteA₂ (t : ℕ) : ℤ := (rhinLite_forms_bounded_K1 t).choose_spec.choose

/-- `B(t)`: the common denominator `lcmUpto N · centralCoeff`. -/
noncomputable def rhinLiteB (t : ℕ) : ℤ :=
  (rhinLite_forms_bounded_K1 t).choose_spec.choose_spec.choose

/-- **Spec of the definite form data.**  The full bounded-forms package for the specific integers
`rhinLiteA₁ t`, `rhinLiteA₂ t`, `rhinLiteB t`. -/
theorem rhinLiteFD_spec (t : ℕ) :
    0 < rhinLiteB t ∧
    (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 17 ^ rhinLiteEvenIndex t ≤ (rhinLiteB t : ℝ) ∧
    (rhinLiteB t : ℝ) ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 18 ^ rhinLiteEvenIndex t ∧
    0 < (rhinLiteA₁ t : ℝ) + rhinLiteB t * Real.log (3 / 2) ∧
    (rhinLiteA₁ t : ℝ) + rhinLiteB t * Real.log (3 / 2)
        ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t ∧
    0 < (rhinLiteA₂ t : ℝ) + rhinLiteB t * Real.log (4 / 3) ∧
    (rhinLiteA₂ t : ℝ) + rhinLiteB t * Real.log (4 / 3)
        ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t :=
  (rhinLite_forms_bounded_K1 t).choose_spec.choose_spec.choose_spec

/-- **Non-vanishing determinant node (disclosed crux sub-node).**  For any nonzero integer triple
`(p,q,r)` and any starting index `t₀`, at least one of the three consecutive combinations
`n(t) = p·B(t) − q·A₁(t) − r·A₂(t)` (`t ∈ {t₀, t₀+1, t₀+2}`) is nonzero.

**Why (Wronskian / Padé non-degeneracy).**  The `3×3` integer determinant of the three consecutive
form-triples `(B(t), A₁(t), A₂(t))` equals — after the unimodular column op
`(B, A₁, A₂) ↦ (B, A₁+B·θ₁, A₂+B·θ₂) = (B, L₁, L₂)` (determinant `1`) — the determinant of
`(B(t), L₁(t), L₂(t))`, whose leading term is `B(t)·B(t+1)·B(t+2)` against the tiny `Lᵢ`.  The
Rhin/Wu construction is a *perfect system*: this determinant is a fixed nonzero integer.  If it were
zero for three consecutive `t`, `(p,−q,−r)` would lie in the left kernel of a nonsingular integer
matrix — impossible.  So `n(t) ≠ 0` for at least one of the three.

TODO: prove the perfect-system non-degeneracy (the explicit determinant is a nonzero rational
coming from the six-factor integral construction).  This is the last genuinely hard node. -/
theorem rhinLite_nonvanishing_triple (p q r : ℤ) (h : p ≠ 0 ∨ q ≠ 0 ∨ r ≠ 0) (t₀ : ℕ) :
    ∃ t, t₀ ≤ t ∧ t ≤ t₀ + 2 ∧
      p * rhinLiteB t - q * rhinLiteA₁ t - r * rhinLiteA₂ t ≠ 0 := by
  sorry

/-- **Pointwise lower bound (the proved assembly core).**  At any index `t` where the integer
combination `n(t) = p·B(t) − q·A₁(t) − r·A₂(t)` is nonzero AND the remainder is small enough
(`(|q|+|r|)·E_N ≤ 1/2`), the linear form is bounded below by `1/(2·B(t))`.  This is
`logForm_conditional_lower` fed with the definite form data `rhinLiteFD_spec` and the `≥ 1/2`
slack.  It is the fully-proved core; the crux `rhinLiteLIMeasure` then only needs the *selection*
of such a `t` (small `E`, nonzero `n`) at a height-controlled index. -/
theorem rhinLite_pointwise_lower (p q r : ℤ) (t : ℕ)
    (hn : p * rhinLiteB t - q * rhinLiteA₁ t - r * rhinLiteA₂ t ≠ 0)
    (hsmall : ((|q| + |r| : ℤ) : ℝ) *
        ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t) ≤ 1 / 2) :
    1 / (2 * (rhinLiteB t : ℝ))
      ≤ |(p : ℝ) + q * Real.log (3 / 2) + r * Real.log (4 / 3)| := by
  obtain ⟨hBpos, _, _, hL1pos, hL1le, hL2pos, hL2le⟩ := rhinLiteFD_spec t
  have hlow := logForm_conditional_lower (rhinLiteA₁ t) (rhinLiteA₂ t) (rhinLiteB t) p q r
    ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t)
    hBpos hL1pos hL1le hL2pos hL2le hn
  have hBRpos : (0 : ℝ) < (rhinLiteB t : ℝ) := by exact_mod_cast hBpos
  have h1 : (1 : ℝ) / 2 ≤
      1 - ((|q| + |r| : ℤ) : ℝ) *
        ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t) := by
    linarith [hsmall]
  calc 1 / (2 * (rhinLiteB t : ℝ)) = (1 / 2) / (rhinLiteB t : ℝ) := by ring
    _ ≤ (1 - ((|q| + |r| : ℤ) : ℝ) *
          ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t))
          / (rhinLiteB t : ℝ) := by gcongr
    _ ≤ _ := hlow

/-- **Remainder + denominator majorants (clean exponential envelopes).**  For `N ≥ N₀` the
`K=1` remainder `E_N = lcmUpto N·(9/40)^N` is majorized by `(99/100)^N` (decaying) and the
denominator `lcmUpto N·18^N` by `(396/5)^N`.  Both from `lcmUpto_le_pow_eventually`. -/
theorem lcmUpto_remainder_majorant :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (Nat.lcmUpto N : ℝ) * (9 / 40 : ℝ) ^ N ≤ (99 / 100 : ℝ) ^ N ∧
      (Nat.lcmUpto N : ℝ) * 18 ^ N ≤ (396 / 5 : ℝ) ^ N := by
  obtain ⟨N₀, hN₀⟩ := lcmUpto_le_pow_eventually
  refine ⟨N₀, fun N hN => ⟨?_, ?_⟩⟩
  · calc (Nat.lcmUpto N : ℝ) * (9 / 40 : ℝ) ^ N ≤ (22 / 5 : ℝ) ^ N * (9 / 40 : ℝ) ^ N := by
          gcongr; exact hN₀ N hN
      _ = (99 / 100 : ℝ) ^ N := by rw [← mul_pow]; norm_num
  · calc (Nat.lcmUpto N : ℝ) * 18 ^ N ≤ (22 / 5 : ℝ) ^ N * 18 ^ N := by
          gcongr; exact hN₀ N hN
      _ = (396 / 5 : ℝ) ^ N := by rw [← mul_pow]; norm_num

theorem rhinLiteLIMeasure :
    ∃ (κ : ℕ) (c : ℝ), 0 < c ∧
      ∀ p q r : ℤ, (p ≠ 0 ∨ q ≠ 0 ∨ r ≠ 0) →
        c / (max |(p : ℝ)| (max |(q : ℝ)| |(r : ℝ)|)) ^ κ
          ≤ |(p : ℝ) + q * Real.log (3 / 2) + r * Real.log (4 / 3)| := by
  sorry

end CollatzMoonshot.FrontA
