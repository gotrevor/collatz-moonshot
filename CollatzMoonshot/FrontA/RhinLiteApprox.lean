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

open Real

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

/-- **Disclosed crux: linear-independence measure of `{1, log(3/2), log(4/3)}`.**

There are `κ : ℕ` and `c > 0` such that for every nonzero integer triple `(p, q, r)`,
`c / H^κ ≤ |p + q·log(3/2) + r·log(4/3)|`, where `H = max(|p|, |q|, |r|)`.

This is the coarse Rhin measure produced by the block subsequence `N = 2000t`.  **Route to a
proof** (all ingredients are already in the repo; only the transference/optimization remains):

* Data: `rhinLiteEven_two_log_forms t` gives `A₁, A₂, B` with `D_N·17^N ≤ B ≤ D_N·18^N`,
  `L₁ = A₁ + B·log(3/2) = D_N·∫_2^3`, `L₂ = A₂ + B·log(4/3) = D_N·∫_3^4`.
* Size: `rhinLiteEvenIntegral_le` / `rhinLiteEvenIntegral_pos_23`/`_34` bound each integral in
  `(0, (9/40)^N]`, so `0 < Lᵢ ≤ D_N·(9/40)^N` (after the `x^{N+1}`→`x^N` bridge, a factor `1/x`).
* Elimination: `elim_identity` gives `B·Λ = n + q·L₁ + r·L₂`, `n = p·B − q·A₁ − r·A₂ ∈ ℤ`.
* Non-vanishing: for a given `(p,q,r)` choose the least `N` with `(|q|+|r|)·D_N·(9/40)^N < 1/2`;
  the determinant of two consecutive form-pairs is nonzero (the two integrals are `> 0` and the
  kernel is not degenerate), so `n ≠ 0` for at least one of two consecutive `N`.  Then
  `|B·Λ| ≥ 1/2`, giving `|Λ| ≥ 1/(2B) ≥ 1/(2·D_N·18^N)`.  With `D_N ≤ 4^N·e^{o(N)}` this is
  `≥ c·H^{−κ}` for a finite `κ` (the coarse Rhin exponent).

Left as the single disclosed obligation of this module; it is a genuine multi-lap analytic
number-theory target (the transference lemma + `lcmUpto` asymptotic), not a citation. -/
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
