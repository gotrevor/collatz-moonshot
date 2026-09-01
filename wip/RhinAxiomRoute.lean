/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.FrontA.PowSeparation

/-!
# [PARKED 2026-09-01] `sep_two_three` from the cited Rhin 1987 axiom — superseded route

This is the axiom-backed proof of `sep_two_three` (`κ = 14`, `c = 1/3^14`, crossover `K = 450`)
that lived in `FrontA/PowSeparation.lean` from 2026-08-31 until the Rhin-lite re-wiring landed
(`FrontA/RhinLiteSep.lean`, `sep_two_three_rhinLite`, which proves the same statement with **no
literature axiom**).  The axiom it consumes, `Assumed.rhin_1987_log_two_three_measure`, is parked
alongside in `wip/Rhin1987.lean` (formerly `CollatzMoonshot/Assumed/Rhin1987.lean`).

Not compiled (`wip/` is outside the `lean_lib`).  To revive: move `wip/Rhin1987.lean` back under
`CollatzMoonshot/Assumed/`, re-add its import here and in `Assumed.lean`, and rename
`sep_two_three` below to avoid the clash with the live theorem.
-/

namespace CollatzMoonshot.FrontA

/-- **Effective irrationality measure of `log₂ 3`, concrete constants (from the Rhin 1987 axiom).**
On the near-critical window (`3^k < 2^m < 2·3^k`, `k ≥ 1`) the Baker linear form obeys
`(1/3^14) / k^14 ≤ m·log2 − k·log3`.  This is the concrete-`(κ,c)` form (`κ = 14`, `c = 1/3^14`)
consumed as `hLF` by `sep_of_linear_form_poly_threshold`.

Proved from `Assumed.rhin_1987_log_two_three_measure` (`|u₀+u₁log2+u₂log3| ≥ 1/H^14`, `H ≥ 2`) at
`(u₀,u₁,u₂) = (0, m, −k)`: then `Λ = m·log2 − k·log3 > 0`, `H = max(m,k) = m ≥ 2` (since `m > k ≥ 1`
on the window), giving `Λ ≥ 1/m^14`, and `m < 3k` gives `1/m^14 ≥ (1/3^14)/k^14`. -/
theorem log23_effective_measure_concrete
    (k m : ℕ) (hk : 1 ≤ k) (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    (1 / 3 ^ 14) / (k : ℝ) ^ 14 ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
  -- `m` sits in `(k, 3k)` on the near-critical window.
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
  -- `Λ > 0`.
  have hΛpos : (0 : ℝ) < (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
    have h3lt : (3 : ℝ) ^ k < (2 : ℝ) ^ m := by exact_mod_cast h1
    have hlog : Real.log ((3 : ℝ) ^ k) < Real.log ((2 : ℝ) ^ m) :=
      Real.log_lt_log (by positivity) h3lt
    rw [Real.log_pow, Real.log_pow] at hlog
    linarith
  -- Apply Rhin at `(0, m, −k)`.  `H = max |m| |−k| = m` (since `m > k`), and `m ≥ 2`.
  have hax := Assumed.rhin_1987_log_two_three_measure 0 (m : ℤ) (-(k : ℤ)) ?_
  · -- rewrite the Rhin bound to `1/m^14 ≤ Λ`
    have hz : max |(m : ℤ)| |-(k : ℤ)| = (m : ℤ) := by
      rw [abs_of_nonneg (by positivity), abs_neg, abs_of_nonneg (by positivity)]
      exact max_eq_left (by exact_mod_cast hkm.le)
    rw [hz, Int.cast_neg] at hax
    have hval : |((0 : ℤ) : ℝ) + ((m : ℤ) : ℝ) * Real.log 2 + -((k : ℤ) : ℝ) * Real.log 3|
        = (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
      rw [abs_of_pos]
      · push_cast; ring
      · push_cast; linarith [hΛpos]
    have haxΛ : 1 / ((m : ℤ) : ℝ) ^ 14 ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 :=
      hval ▸ hax
    -- `(1/3^14)/k^14 ≤ 1/m^14 ≤ Λ` since `m < 3k`.
    have hmlt : ((m : ℤ) : ℝ) ≤ 3 * (k : ℝ) := by push_cast; exact_mod_cast hm3k.le
    have hstep : (1 / 3 ^ 14) / (k : ℝ) ^ 14 ≤ 1 / ((m : ℤ) : ℝ) ^ 14 := by
      have hle : ((m : ℤ) : ℝ) ^ 14 ≤ 3 ^ 14 * (k : ℝ) ^ 14 := by
        calc ((m : ℤ) : ℝ) ^ 14 ≤ (3 * (k : ℝ)) ^ 14 :=
              pow_le_pow_left₀ (by positivity) hmlt 14
          _ = 3 ^ 14 * (k : ℝ) ^ 14 := by rw [mul_pow]
      have hmpos : (0 : ℝ) < ((m : ℤ) : ℝ) ^ 14 := by
        have : (0 : ℝ) < ((m : ℤ) : ℝ) := by exact_mod_cast (by omega : 0 < m)
        positivity
      have h1 := one_div_le_one_div_of_le hmpos hle
      rw [div_div]; exact h1
    exact le_trans hstep haxΛ
  · -- `max |m| |−k| ≥ 2` since `m ≥ 2`
    rw [abs_of_nonneg (by positivity : (0:ℤ) ≤ (m:ℤ))]
    have : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (by omega : 2 ≤ m)
    exact le_trans this (le_max_left _ _)

/-- **Effective irrationality measure of `log₂ 3` (existential audit surface).**  Repackages
`log23_effective_measure_concrete` in the `∃ κ c` shape used elsewhere (`κ = 14`, `c = 1/3^14`). -/
theorem log23_effective_measure :
    ∃ (κ : ℕ) (c : ℝ), 0 < c ∧
      ∀ k m : ℕ, 1 ≤ k → 3 ^ k < 2 ^ m → 2 ^ m < 2 * 3 ^ k →
        c / (k : ℝ) ^ κ ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 :=
  ⟨14, 1 / 3 ^ 14, by positivity, fun k m hk h1 h2 => log23_effective_measure_concrete k m hk h1 h2⟩

/-- **Weak power separation `β = 1/3` (sorry-free, modulo the cited Rhin 1987 axiom).**  For the
near-critical power `2^m` just above `3^k` (`3^k < 2^m < 2·3^k`) with `k ≥ 6`,
`3^(3k) ≤ (2^m − 3^k)^3 · 2^k`, i.e. `2^m − 3^k ≥ 3^k · 2^(−k/3)`.

Discharged by instantiating `sep_of_linear_form_poly_threshold` at the concrete Rhin measure
constants `κ = 14`, `c = 1/3^14` (`log23_effective_measure_concrete`), threshold `K = 450` (past the
crossover point `k ≈ 435`), crossover `crossover_exp_450`, and the finite check
`sep_two_three_small_450` on `6 ≤ k < 450`.  The sole remaining mathematical input is the cited
`Assumed.rhin_1987_log_two_three_measure`; everything else is elementary + a `native_decide` table. -/
theorem sep_two_three (k m : ℕ) (hk : 6 ≤ k) (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  refine sep_of_linear_form_poly_threshold (1 / 3 ^ 14) 14 450 ?_ ?_ ?_ k m hk h1 h2
  · intro k m hk450 h1 h2
    exact log23_effective_measure_concrete k m (by omega) h1 h2
  · intro k hk450
    have hc := crossover_exp_450 k hk450
    rw [show (1 : ℝ) / 3 ^ 14 * Real.exp ((k : ℝ) / 3 * Real.log 2)
          = Real.exp ((k : ℝ) / 3 * Real.log 2) / 3 ^ 14 by ring,
        le_div_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ 14)]
    linarith [hc, mul_comm ((3 : ℝ) ^ 14) ((k : ℝ) ^ 14)]
  · intro k m hk6 hklt h1 h2
    exact sep_two_three_small_450 k m hk6 hklt h1 h2


end CollatzMoonshot.FrontA
