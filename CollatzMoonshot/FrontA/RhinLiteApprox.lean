/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.RhinLiteLogForm
import CollatzMoonshot.FrontA.PowSeparation

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

/-- **Disclosed crux: linear-independence measure of `{1, log(3/2), log(4/3)}`.**

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
theorem rhinLiteLIMeasure :
    ∃ (κ : ℕ) (c : ℝ), 0 < c ∧
      ∀ p q r : ℤ, (p ≠ 0 ∨ q ≠ 0 ∨ r ≠ 0) →
        c / (max |(p : ℝ)| (max |(q : ℝ)| |(r : ℝ)|)) ^ κ
          ≤ |(p : ℝ) + q * Real.log (3 / 2) + r * Real.log (4 / 3)| := by
  sorry

/-- **Effective irrationality measure of `log₂ 3`, proved from the crux.**  There are `κ : ℕ` and
`c > 0` such that on the near-critical window (`3^k < 2^m < 2·3^k`, `k ≥ 1`) the Baker linear form
obeys `c / k^κ ≤ m·log2 − k·log3`.  This is exactly the `hLF` shape consumed by
`sep_of_linear_form_poly`; it is derived from `rhinLiteLIMeasure` by the change of basis
`linForm_eq_log23` (with `p = 0`, `q = m − 2k`, `r = m − k`, so the combination is homogeneous and
equals `Λ`), the sign `Λ > 0` (from `3^k < 2^m`), and the crude height bound `H ≤ 2k`. -/
theorem log23_effective_measure :
    ∃ (κ : ℕ) (c : ℝ), 0 < c ∧
      ∀ k m : ℕ, 1 ≤ k → 3 ^ k < 2 ^ m → 2 ^ m < 2 * 3 ^ k →
        c / (k : ℝ) ^ κ ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
  obtain ⟨κ, c, hc, hmeas⟩ := rhinLiteLIMeasure
  refine ⟨κ, c / 2 ^ κ, by positivity, ?_⟩
  intro k m hk h1 h2
  -- `m` sits in `[k, 3k)` on the near-critical window.
  have hkm : k < m := by
    have h2k : (2 : ℕ) ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
    have : (2 : ℕ) ^ k < 2 ^ m := lt_of_le_of_lt h2k h1
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hm3k : m < 3 * k := by
    have hbnd : 2 * 3 ^ k ≤ 2 ^ (3 * k) := by
      calc 2 * 3 ^ k ≤ 2 * 4 ^ k := by gcongr; norm_num
        _ ≤ 2 ^ k * 4 ^ k := by
            gcongr
            calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        _ = 2 ^ (3 * k) := by rw [← Nat.mul_pow]; norm_num [pow_mul]
    have : (2 : ℕ) ^ m < 2 ^ (3 * k) := lt_of_lt_of_le h2 hbnd
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  -- The homogeneous triple.
  set q : ℤ := (m : ℤ) - 2 * k with hqdef
  set r : ℤ := (m : ℤ) - k with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]; have : (k : ℤ) < m := by exact_mod_cast hkm
    omega
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hnz : ((0 : ℤ) ≠ 0 ∨ q ≠ 0 ∨ r ≠ 0) := Or.inr (Or.inr hrne)
  have hkey := hmeas 0 q r hnz
  -- The combination equals `Λ`.
  have hΛpos : (0 : ℝ) < (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
    have h3lt : (3 : ℝ) ^ k < (2 : ℝ) ^ m := by exact_mod_cast h1
    have hlog : Real.log ((3 : ℝ) ^ k) < Real.log ((2 : ℝ) ^ m) :=
      Real.log_lt_log (by positivity) h3lt
    rw [Real.log_pow, Real.log_pow] at hlog
    linarith
  have hval : ((0 : ℤ) : ℝ) + (q : ℝ) * Real.log (3 / 2) + (r : ℝ) * Real.log (4 / 3)
      = (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
    rw [hqdef, hrdef]; push_cast
    rw [zero_add]
    have := linForm_eq_log23 (k : ℝ) (m : ℝ)
    linarith [this]
  rw [hval] at hkey
  rw [abs_of_pos hΛpos] at hkey
  -- Bound the height `H ≤ 2k` and monotonize.
  set H : ℝ := max |((0 : ℤ) : ℝ)| (max |(q : ℝ)| |(r : ℝ)|) with hHdef
  have hqbound : |(q : ℝ)| ≤ 2 * k := by
    rw [hqdef]; push_cast; rw [abs_le]
    refine ⟨by nlinarith [(show (k : ℝ) ≤ m by exact_mod_cast hkm.le),
             (show (0 : ℝ) ≤ k by positivity)], by nlinarith
             [(show (m : ℝ) ≤ 3 * k by exact_mod_cast hm3k.le),
              (show (0 : ℝ) ≤ k by positivity)]⟩
  have hrbound : |(r : ℝ)| ≤ 2 * k := by
    rw [hrdef]; push_cast; rw [abs_le]; constructor <;> nlinarith
      [(show (m : ℝ) ≤ 3 * k by exact_mod_cast hm3k.le),
       (show (k : ℝ) ≤ m by exact_mod_cast hkm.le),
       (show (0 : ℝ) ≤ k by positivity)]
  have hHle : H ≤ 2 * k := by
    rw [hHdef]
    simp only [Int.cast_zero, abs_zero]
    refine max_le (by positivity) (max_le hqbound hrbound)
  have hHpos : 0 < H := by
    rw [hHdef]
    have : (1 : ℝ) ≤ |(r : ℝ)| := by
      rw [abs_of_pos (by exact_mod_cast hrpos)]; exact_mod_cast hrpos
    calc (0 : ℝ) < 1 := one_pos
      _ ≤ |(r : ℝ)| := this
      _ ≤ max |(q : ℝ)| |(r : ℝ)| := le_max_right _ _
      _ ≤ max |((0 : ℤ) : ℝ)| (max |(q : ℝ)| |(r : ℝ)|) := le_max_right _ _
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  -- `c/2^κ / k^κ = c/(2k)^κ ≤ c/H^κ ≤ Λ`.
  have hstep : c / 2 ^ κ / (k : ℝ) ^ κ ≤ c / H ^ κ := by
    rw [div_div, ← mul_pow]
    have hHκpos : (0 : ℝ) < H ^ κ := pow_pos hHpos κ
    have h2kκpos : (0 : ℝ) < (2 * (k : ℝ)) ^ κ := by positivity
    apply div_le_div_of_nonneg_left hc.le hHκpos
    exact pow_le_pow_left₀ hHpos.le hHle κ
  exact le_trans hstep hkey

end CollatzMoonshot.FrontA
