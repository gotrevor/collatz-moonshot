/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.RhinLiteApprox

/-!
# `sep_two_three` from the Rhin-lite measure — explicit constants and the finite crossover

This module retires the cited Rhin 1987 axiom on the two-block exclusion path.  It re-wires the
separation statement `sep_two_three` (the sink node of `b + d ≤ 5`, see `PowSeparation.lean`) onto
the **proved** Rhin-lite linear-independence measure of `{1, log(3/2), log(4/3)}`
(`rhinLiteLIMeasure`, `RhinLiteApprox.lean`) instead of `Assumed.rhin_1987_log_two_three_measure`.

## Why a direct re-wiring is impossible, and what is done instead

`rhinLiteLIMeasure` is *existential*: `∃ κ c, …`.  Its constant is `c = 1/(2C)` with
`C = (396/5)^(6000+N₀)·6^κ`, where `N₀` is the (classical, `isLittleO`-extracted) threshold of
`lcmUpto_le_pow_eventually`.  An opaque `c` gives no concrete crossover `K`, so the finite range
`6 ≤ k < K` of `sep_of_linear_form_poly_threshold` cannot even be stated.  The fix is to make
every constant explicit:

* **`N₀ = 0` on the even block indices.**  `lcmUpto (2000t) ≤ (22/5)^(2000t)` for *every* `t ≥ 1`:
  a kernel certificate (`decide +kernel`, eight monotone blocks) for `t ≤ 30`, and the mathlib
  Chebyshev bound `ψ N ≤ N·log 4 + 2√N·log N` for `N ≥ 62000`, where the subexponential term is
  absorbed by the elementary estimate `4·log s ≤ s/11` (`s = √N ≥ 248`).
* **`κ = 436`**, the least integer with `(100/99)^κ ≥ 396/5` (`435` fails), and
  `C = (396/5)^6000 · 6^436`, so `c = rhinLiteSepC = 1/(2C)`, `log₂(1/c) ≈ 38972`.
* **Change of basis.**  On the near-critical window `3^k < 2^m < 2·3^k` the Baker form
  `Λ = m·log2 − k·log3` is the homogeneous combination `(m−2k)·log(3/2) + (m−k)·log(4/3)` of height
  `≤ k` (`k < m ≤ 2k`), so the measure gives `Λ ≥ c/k^436` (`rhinLite_log23_measure`).
* **Crossover `K = 141000`** (`= 3·47000`): `k^436 ≤ c·2^(k/3)` for `k ≥ K`
  (`crossover_exp_436_141000`; base case a kernel check on `~14000`-digit naturals, margin
  `≈ 133` bits; step `((n+1)/n)^436 ≤ 2^(1/3)` for `n ≥ 5·436`).
* **Finite range `450 ≤ k < 141000`** via five consecutive-convergent brackets of `θ = log₂3`
  (denominators `306, 665, 15601, 31867, 79335, 111202`), each fed to the sharp best-approximation
  engine `sep_of_bracket_sharp` with the bracket gap bounded below by the next same-side
  convergent/semiconvergent.  Eight integer power comparisons, the largest `2^478245 < 3^301739`
  (`144k` digits), all `decide +kernel` (axioms `[propext]`).  `k < 450` is the existing table
  `sep_two_three_small_450`.

The result `sep_two_three_rhinLite` carries no `sorryAx` and no literature axiom: its ledger is
the trust base plus the `native_decide` certificates already inside the Rhin-lite tower.

## Why not sharpen `κ` instead

Even Hanson's `lcm(1..n) < 3^n` (κ ≈ 11) only moves the crossover from `≈ 139k` to `≈ 104k`,
because `log C ≈ 6000·log(18·base)` — the `2000`-index block spacing plus the three-index
non-vanishing window — dominates `κ·log k`.  Since the convergent denominators of `log₂3` jump
from `190537` to `10590737`, any `K < 190537` costs the same certificates; there is nothing to gain.
-/

namespace CollatzMoonshot.FrontA

open Real

set_option exponentiation.threshold 100000000
set_option maxRecDepth 100000

/-! ### The `lcmUpto` majorant without threshold on the even block indices -/

/-- Block transfer: a certificate at the top index of a block, scaled at its bottom index, covers
the whole block. -/
theorem lcmUpto_block_le {a b N : ℕ} (hN : 2000 * a ≤ N) (hNb : N ≤ 2000 * b)
    (hcert : Nat.lcmUpto (2000 * b) * 5 ^ (2000 * a) ≤ 22 ^ (2000 * a)) :
    Nat.lcmUpto N * 5 ^ N ≤ 22 ^ N := by
  have hmono : Nat.lcmUpto N ≤ Nat.lcmUpto (2000 * b) :=
    Nat.le_of_dvd (Nat.lcmUpto_pos _) (lcmUpto_dvd_of_le hNb)
  obtain ⟨e, rfl⟩ : ∃ e, N = 2000 * a + e := ⟨N - 2000 * a, by omega⟩
  rw [pow_add, pow_add]
  calc Nat.lcmUpto (2000 * a + e) * (5 ^ (2000 * a) * 5 ^ e)
      ≤ Nat.lcmUpto (2000 * b) * (5 ^ (2000 * a) * 5 ^ e) := by gcongr
    _ = (Nat.lcmUpto (2000 * b) * 5 ^ (2000 * a)) * 5 ^ e := by ring
    _ ≤ 22 ^ (2000 * a) * 5 ^ e := by gcongr
    _ ≤ 22 ^ (2000 * a) * 22 ^ e := by gcongr; norm_num

/-! The eight block certificates (kernel-checked; stated in the exact syntactic shape consumed by
`lcmUpto_block_le`, so that `exact` never has to evaluate them in the elaborator). -/
theorem lcmUpto_cert_1 : Nat.lcmUpto (2000 * 1) * 5 ^ (2000 * 1) ≤ 22 ^ (2000 * 1) := by
  decide +kernel
theorem lcmUpto_cert_2 : Nat.lcmUpto (2000 * 2) * 5 ^ (2000 * 2) ≤ 22 ^ (2000 * 2) := by
  decide +kernel
theorem lcmUpto_cert_3_4 : Nat.lcmUpto (2000 * 4) * 5 ^ (2000 * 3) ≤ 22 ^ (2000 * 3) := by
  decide +kernel
theorem lcmUpto_cert_5_7 : Nat.lcmUpto (2000 * 7) * 5 ^ (2000 * 5) ≤ 22 ^ (2000 * 5) := by
  decide +kernel
theorem lcmUpto_cert_8_11 : Nat.lcmUpto (2000 * 11) * 5 ^ (2000 * 8) ≤ 22 ^ (2000 * 8) := by
  decide +kernel
theorem lcmUpto_cert_12_17 : Nat.lcmUpto (2000 * 17) * 5 ^ (2000 * 12) ≤ 22 ^ (2000 * 12) := by
  decide +kernel
theorem lcmUpto_cert_18_26 : Nat.lcmUpto (2000 * 26) * 5 ^ (2000 * 18) ≤ 22 ^ (2000 * 18) := by
  decide +kernel
theorem lcmUpto_cert_27_30 : Nat.lcmUpto (2000 * 30) * 5 ^ (2000 * 27) ≤ 22 ^ (2000 * 27) := by
  decide +kernel

/-- Small block indices `1 ≤ t ≤ 30`: `lcmUpto (2000t)·5^(2000t) ≤ 22^(2000t)` (kernel). -/
theorem lcmUpto_even_small (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ 30) :
    Nat.lcmUpto (2000 * t) * 5 ^ (2000 * t) ≤ 22 ^ (2000 * t) := by
  rcases (by omega : t = 1 ∨ t = 2 ∨ (3 ≤ t ∧ t ≤ 4) ∨ (5 ≤ t ∧ t ≤ 7) ∨ (8 ≤ t ∧ t ≤ 11) ∨
      (12 ≤ t ∧ t ≤ 17) ∨ (18 ≤ t ∧ t ≤ 26) ∨ (27 ≤ t ∧ t ≤ 30)) with
    h | h | h | h | h | h | h | h
  · subst h; exact lcmUpto_cert_1
  · subst h; exact lcmUpto_cert_2
  · exact lcmUpto_block_le (a := 3) (b := 4) (by omega) (by omega) lcmUpto_cert_3_4
  · exact lcmUpto_block_le (a := 5) (b := 7) (by omega) (by omega) lcmUpto_cert_5_7
  · exact lcmUpto_block_le (a := 8) (b := 11) (by omega) (by omega) lcmUpto_cert_8_11
  · exact lcmUpto_block_le (a := 12) (b := 17) (by omega) (by omega) lcmUpto_cert_12_17
  · exact lcmUpto_block_le (a := 18) (b := 26) (by omega) (by omega) lcmUpto_cert_18_26
  · exact lcmUpto_block_le (a := 27) (b := 30) (by omega) (by omega) lcmUpto_cert_27_30

/-- **Explicit Chebyshev absorption.**  For `N ≥ 62000`, `lcmUpto N ≤ (22/5)^N`.  From
`lcmUpto_log_le_chebyshev` (`log lcmUpto N ≤ N·log 4 + 2√N·log N`) and the elementary bound
`4·log s ≤ s/11 ≤ log(11/10)·s` for `s = √N ≥ 248` (via `log s ≤ log 256 + s/256 − 1`). -/
theorem lcmUpto_le_pow_of_ge (N : ℕ) (hN : 62000 ≤ N) :
    (Nat.lcmUpto N : ℝ) ≤ (22 / 5 : ℝ) ^ N := by
  have hNR : (62000 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set s := Real.sqrt (N : ℝ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s * s = N := Real.mul_self_sqrt (by positivity)
  have hs248 : (248 : ℝ) ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hspos : 0 < s := by linarith
  -- log s ≤ 8 log 2 + s/256 − 1
  have hlogs : Real.log s ≤ 8 * Real.log 2 + s / 256 - 1 := by
    have h1 : Real.log s = Real.log 256 + Real.log (s / 256) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      congr 1; field_simp
    have h2 : Real.log (s / 256) ≤ s / 256 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log 256 = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlogN : Real.log (N : ℝ) = 2 * Real.log s := by
    rw [← hs2, Real.log_mul hspos.ne' hspos.ne']; ring
  have hlog11 : (1 : ℝ) / 11 ≤ Real.log (11 / 10) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 11 / 10)
    norm_num at this ⊢; linarith
  have hlog11s : (1 : ℝ) / 11 * s ≤ Real.log (11 / 10) * s :=
    mul_le_mul_of_nonneg_right hlog11 hs0
  -- 4 log s ≤ log(11/10)·s
  have h4 : 4 * Real.log s ≤ Real.log (11 / 10) * s := by nlinarith
  -- 2√N·log N ≤ log(11/10)·N
  have hkey : 2 * s * Real.log (N : ℝ) ≤ Real.log (11 / 10) * N := by
    rw [hlogN, ← hs2]; nlinarith
  have hcheb := lcmUpto_log_le_chebyshev N
  have hlog225 : Real.log (22 / 5) = Real.log 4 + Real.log (11 / 10) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hfinal : Real.log (Nat.lcmUpto N : ℝ) ≤ (N : ℝ) * Real.log (22 / 5) := by
    rw [hlog225]; nlinarith
  have hpos : (0 : ℝ) < Nat.lcmUpto N := by exact_mod_cast Nat.lcmUpto_pos N
  rw [← Real.log_le_log_iff hpos (by positivity), Real.log_pow]
  exact hfinal

/-- **The threshold-free majorant on the even block indices.**  `lcmUpto (2000t) ≤ (22/5)^(2000t)`
for every `t ≥ 1` — the `N₀ = 0` replacement for `lcmUpto_le_pow_eventually`. -/
theorem lcmUpto_even_le_pow (t : ℕ) (ht : 1 ≤ t) :
    (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) ≤ (22 / 5 : ℝ) ^ rhinLiteEvenIndex t := by
  rw [rhinLiteEvenIndex_eq]
  rcases le_or_gt t 30 with h | h
  · have hc := lcmUpto_even_small t ht h
    have hcR : (Nat.lcmUpto (2000 * t) : ℝ) * 5 ^ (2000 * t) ≤ 22 ^ (2000 * t) := by
      exact_mod_cast hc
    rw [div_pow, le_div_iff₀ (by positivity)]; exact hcR
  · exact lcmUpto_le_pow_of_ge _ (by omega)

/-! ### The selection envelope and the measure with explicit constants -/

/-- `(100/99)^436 ≥ 396/5`, hence `log(396/5) ≤ 436·log(100/99)` — the explicit exponent. -/
theorem log_396_5_le_436 : Real.log (396 / 5) ≤ ((436 : ℕ) : ℝ) * Real.log (100 / 99) := by
  have hnat : 396 * 99 ^ 436 ≤ 5 * 100 ^ 436 := by decide +kernel
  have h : (396 / 5 : ℝ) ≤ (100 / 99 : ℝ) ^ (436 : ℕ) := by
    rw [div_pow, div_le_div_iff₀ (by norm_num) (by positivity)]
    exact_mod_cast hnat
  calc Real.log (396 / 5) ≤ Real.log ((100 / 99 : ℝ) ^ (436 : ℕ)) :=
        Real.log_le_log (by norm_num) h
    _ = ((436 : ℕ) : ℝ) * Real.log (100 / 99) := by rw [Real.log_pow]

/-- **Selection + envelope, explicit form.**  Given any exponent `κ` with
`log(396/5) ≤ κ·log(100/99)` and the threshold-free majorant `lcmUpto N(t) ≤ (22/5)^N(t)`
(`t ≥ 1`), the selection of `rhinLite_selection_envelope` goes through with the explicit constant
`C = (396/5)^6000 · 6^κ` (no `N₀`). -/
theorem rhinLite_selection_envelope_of_majorant (κ : ℕ)
    (hκ : Real.log (396 / 5) ≤ (κ : ℝ) * Real.log (100 / 99))
    (hmaj : ∀ t : ℕ, 1 ≤ t →
      (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) ≤ (22 / 5 : ℝ) ^ rhinLiteEvenIndex t) :
    ∀ (S : ℕ) (H : ℝ), 1 ≤ H → (S : ℝ) ≤ 2 * H →
      ∃ t₀ : ℕ,
        (∀ t, t₀ ≤ t →
          (S : ℝ) * ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) *
            (9 / 40 : ℝ) ^ rhinLiteEvenIndex t) ≤ 1 / 2) ∧
        (∀ t, t₀ ≤ t → t ≤ t₀ + 2 →
          (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 18 ^ rhinLiteEvenIndex t
            ≤ ((396 / 5 : ℝ) ^ 6000 * 6 ^ κ) * H ^ κ) := by
  intro S H hH hSH
  set L99 : ℝ := Real.log (100 / 99) with hL99def
  set L396 : ℝ := Real.log (396 / 5) with hL396def
  have hL99pos : 0 < L99 := Real.log_pos (by norm_num)
  have hL396pos : 0 < L396 := Real.log_pos (by norm_num)
  set ρ : ℝ := L396 / L99 with hρdef
  have hρκ : ρ ≤ κ := by rw [hρdef, div_le_iff₀ hL99pos]; exact hκ
  set y : ℝ := 2 * (S : ℝ) + 2 with hydef
  have hy2 : (2 : ℝ) ≤ y := by
    rw [hydef]; have := Nat.cast_nonneg (α := ℝ) S; linarith
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hypos : (0 : ℝ) < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  set T : ℝ := Real.log y / L99 with hTdef
  have hTpos : 0 < T := div_pos hlogy hL99pos
  set t₀ : ℕ := ⌈T / 2000⌉₊ with ht₀def
  have ht₀pos : 1 ≤ t₀ := by
    rw [ht₀def]
    apply Nat.one_le_iff_ne_zero.mpr
    intro h
    rw [Nat.ceil_eq_zero] at h
    linarith [div_pos hTpos (by norm_num : (0 : ℝ) < 2000)]
  have hNt0_ge : T ≤ 2000 * (t₀ : ℝ) := by
    have := Nat.le_ceil (T / 2000)
    rw [ht₀def]; nlinarith [this]
  have hNt0_lt : (2000 : ℝ) * (t₀ : ℝ) < T + 2000 := by
    have := Nat.ceil_lt_add_one (a := T / 2000) (by positivity)
    rw [ht₀def]; nlinarith [this]
  have hidx : ∀ t : ℕ, (rhinLiteEvenIndex t : ℝ) = 2000 * (t : ℝ) := by
    intro t; rw [rhinLiteEvenIndex_eq]; push_cast; ring
  have hNge : ∀ t, t₀ ≤ t → T ≤ (rhinLiteEvenIndex t : ℝ) := by
    intro t ht
    rw [hidx t]
    have : (t₀ : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hmaj1 : ∀ t, t₀ ≤ t →
      (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t
        ≤ (99 / 100 : ℝ) ^ rhinLiteEvenIndex t := by
    intro t ht
    calc (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t
        ≤ (22 / 5 : ℝ) ^ rhinLiteEvenIndex t * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t := by
          gcongr; exact hmaj t (le_trans ht₀pos ht)
      _ = (99 / 100 : ℝ) ^ rhinLiteEvenIndex t := by rw [← mul_pow]; norm_num
  have hmaj2 : ∀ t, t₀ ≤ t →
      (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 18 ^ rhinLiteEvenIndex t
        ≤ (396 / 5 : ℝ) ^ rhinLiteEvenIndex t := by
    intro t ht
    calc (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 18 ^ rhinLiteEvenIndex t
        ≤ (22 / 5 : ℝ) ^ rhinLiteEvenIndex t * 18 ^ rhinLiteEvenIndex t := by
          gcongr; exact hmaj t (le_trans ht₀pos ht)
      _ = (396 / 5 : ℝ) ^ rhinLiteEvenIndex t := by rw [← mul_pow]; norm_num
  refine ⟨t₀, ?_, ?_⟩
  · -- smallness
    intro t ht
    have hm1 := hmaj1 t ht
    have hSnn : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg _
    have hstep : (S : ℝ) * ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) *
        (9 / 40 : ℝ) ^ rhinLiteEvenIndex t) ≤ (S : ℝ) * (99 / 100 : ℝ) ^ rhinLiteEvenIndex t :=
      mul_le_mul_of_nonneg_left hm1 hSnn
    have hbasepos : (0 : ℝ) < (99 / 100 : ℝ) := by norm_num
    have hbasele1 : (99 / 100 : ℝ) ≤ 1 := by norm_num
    have hpow_rpow : (99 / 100 : ℝ) ^ rhinLiteEvenIndex t
        = (99 / 100 : ℝ) ^ ((rhinLiteEvenIndex t : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    have hdec1 : (99 / 100 : ℝ) ^ ((rhinLiteEvenIndex t : ℕ) : ℝ) ≤ (99 / 100 : ℝ) ^ T :=
      Real.rpow_le_rpow_of_exponent_ge hbasepos hbasele1 (hNge t ht)
    have hval : (99 / 100 : ℝ) ^ T = 1 / y := by
      rw [hTdef, Real.rpow_def_of_pos hbasepos]
      have hlog : Real.log (99 / 100) = - L99 := by
        rw [hL99def, show (99 / 100 : ℝ) = (100 / 99 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [hlog]
      rw [show (-L99) * (Real.log y / L99) = -(Real.log y) by field_simp]
      rw [Real.exp_neg, Real.exp_log hypos, one_div]
    have hle_y : (99 / 100 : ℝ) ^ rhinLiteEvenIndex t ≤ 1 / y := by
      rw [hpow_rpow]; exact le_trans hdec1 hval.le
    have : (S : ℝ) * (99 / 100 : ℝ) ^ rhinLiteEvenIndex t ≤ (S : ℝ) * (1 / y) :=
      mul_le_mul_of_nonneg_left hle_y hSnn
    have hfin : (S : ℝ) * (1 / y) ≤ 1 / 2 := by
      rw [hydef, mul_one_div, div_le_iff₀ (by positivity)]; nlinarith [hSnn]
    calc (S : ℝ) * ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) *
            (9 / 40 : ℝ) ^ rhinLiteEvenIndex t)
        ≤ (S : ℝ) * (99 / 100 : ℝ) ^ rhinLiteEvenIndex t := hstep
      _ ≤ (S : ℝ) * (1 / y) := this
      _ ≤ 1 / 2 := hfin
  · -- envelope
    intro t ht htle
    have hm2 := hmaj2 t ht
    have hNt_le : (rhinLiteEvenIndex t : ℝ) ≤ T + 6000 := by
      rw [hidx t]
      have h1 : (t : ℝ) ≤ (t₀ : ℝ) + 2 := by exact_mod_cast htle
      nlinarith [hNt0_lt, h1]
    have hb1 : (1 : ℝ) < (396 / 5 : ℝ) := by norm_num
    have hbpos : (0 : ℝ) < (396 / 5 : ℝ) := by norm_num
    have hpow_rpow : (396 / 5 : ℝ) ^ rhinLiteEvenIndex t
        = (396 / 5 : ℝ) ^ ((rhinLiteEvenIndex t : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    have hinc1 : (396 / 5 : ℝ) ^ ((rhinLiteEvenIndex t : ℕ) : ℝ)
        ≤ (396 / 5 : ℝ) ^ (T + 6000) :=
      Real.rpow_le_rpow_of_exponent_le hb1.le hNt_le
    have hsplit1 : (396 / 5 : ℝ) ^ (T + 6000)
        = (396 / 5 : ℝ) ^ (6000 : ℝ) * (396 / 5 : ℝ) ^ T := by
      rw [add_comm, Real.rpow_add hbpos]
    have hyρ : (396 / 5 : ℝ) ^ T = y ^ ρ := by
      rw [hTdef, Real.rpow_def_of_pos hbpos, Real.rpow_def_of_pos hypos, hρdef, hL396def]
      congr 1; field_simp
    have hyρκ : y ^ ρ ≤ y ^ (κ : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 hρκ
    have hyκ_nat : y ^ (κ : ℝ) = y ^ κ := Real.rpow_natCast y κ
    have hy6H : y ≤ 6 * H := by rw [hydef]; nlinarith [hSH, hH]
    have hyκ6 : (y : ℝ) ^ κ ≤ (6 * H) ^ κ :=
      pow_le_pow_left₀ (by positivity) hy6H κ
    have h6H : (6 * H : ℝ) ^ κ = 6 ^ κ * H ^ κ := by rw [mul_pow]
    have hchainT : (396 / 5 : ℝ) ^ T ≤ 6 ^ κ * H ^ κ := by
      calc (396 / 5 : ℝ) ^ T = y ^ ρ := hyρ
        _ ≤ y ^ (κ : ℝ) := hyρκ
        _ = y ^ κ := hyκ_nat
        _ ≤ (6 * H) ^ κ := hyκ6
        _ = 6 ^ κ * H ^ κ := h6H
    have hr6000 : (396 / 5 : ℝ) ^ (6000 : ℝ) = (396 / 5 : ℝ) ^ (6000 : ℕ) := by
      rw [show (6000 : ℝ) = ((6000 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 18 ^ rhinLiteEvenIndex t
        ≤ (396 / 5 : ℝ) ^ rhinLiteEvenIndex t := hm2
      _ = (396 / 5 : ℝ) ^ ((rhinLiteEvenIndex t : ℕ) : ℝ) := hpow_rpow
      _ ≤ (396 / 5 : ℝ) ^ (T + 6000) := hinc1
      _ = (396 / 5 : ℝ) ^ (6000 : ℝ) * (396 / 5 : ℝ) ^ T := hsplit1
      _ ≤ (396 / 5 : ℝ) ^ (6000 : ℝ) * (6 ^ κ * H ^ κ) :=
            mul_le_mul_of_nonneg_left hchainT (by positivity)
      _ = ((396 / 5 : ℝ) ^ 6000 * 6 ^ κ) * H ^ κ := by rw [hr6000]; ring

/-- **The measure from an envelope (generic constants).**  This is the assembly of
`rhinLiteLIMeasure` with the selection envelope abstracted: any `(κ, C)` envelope yields the
linear-independence measure with `c = 1/(2C)`. -/
theorem rhinLiteLIMeasure_of_envelope (κ : ℕ) (C : ℝ) (_hCpos : 0 < C)
    (henv : ∀ (S : ℕ) (H : ℝ), 1 ≤ H → (S : ℝ) ≤ 2 * H →
      ∃ t₀ : ℕ,
        (∀ t, t₀ ≤ t →
          (S : ℝ) * ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) *
            (9 / 40 : ℝ) ^ rhinLiteEvenIndex t) ≤ 1 / 2) ∧
        (∀ t, t₀ ≤ t → t ≤ t₀ + 2 →
          (Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 18 ^ rhinLiteEvenIndex t
            ≤ C * H ^ κ)) :
    ∀ p q r : ℤ, (p ≠ 0 ∨ q ≠ 0 ∨ r ≠ 0) →
      (1 / (2 * C)) / (max |(p : ℝ)| (max |(q : ℝ)| |(r : ℝ)|)) ^ κ
        ≤ |(p : ℝ) + q * Real.log (3 / 2) + r * Real.log (4 / 3)| := by
  intro p q r hpqr
  set H : ℝ := max |(p : ℝ)| (max |(q : ℝ)| |(r : ℝ)|) with hHdef
  have hqleH : |(q : ℝ)| ≤ H := le_trans (le_max_left _ _) (le_max_right _ _)
  have hrleH : |(r : ℝ)| ≤ H := le_trans (le_max_right _ _) (le_max_right _ _)
  have hpleH : |(p : ℝ)| ≤ H := le_max_left _ _
  have hH1 : 1 ≤ H := by
    rcases hpqr with hp | hq | hr
    · have hb : (1 : ℝ) ≤ |(p : ℝ)| := by exact_mod_cast Int.one_le_abs hp
      linarith [hpleH]
    · have hb : (1 : ℝ) ≤ |(q : ℝ)| := by exact_mod_cast Int.one_le_abs hq
      linarith [hqleH]
    · have hb : (1 : ℝ) ≤ |(r : ℝ)| := by exact_mod_cast Int.one_le_abs hr
      linarith [hrleH]
  set S : ℕ := (|q| + |r|).toNat with hSdef
  have hSnonneg : (0 : ℤ) ≤ |q| + |r| := by positivity
  have hSZ : (S : ℤ) = |q| + |r| := by rw [hSdef]; exact Int.toNat_of_nonneg hSnonneg
  have hSint : (S : ℝ) = ((|q| + |r| : ℤ) : ℝ) := by
    rw [show (S : ℝ) = ((S : ℤ) : ℝ) by push_cast; ring, hSZ]
  have hScast : (S : ℝ) = |(q : ℝ)| + |(r : ℝ)| := by rw [hSint]; push_cast; ring
  have hSH : (S : ℝ) ≤ 2 * H := by rw [hScast]; linarith [hqleH, hrleH]
  obtain ⟨t₀, hsmall, henvt⟩ := henv S H hH1 hSH
  obtain ⟨t, ht₀, htle, hn⟩ := rhinLite_nonvanishing_triple p q r hpqr t₀
  have hsm : ((|q| + |r| : ℤ) : ℝ) *
      ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * (9 / 40 : ℝ) ^ rhinLiteEvenIndex t) ≤ 1 / 2 := by
    rw [← hSint]; exact hsmall t ht₀
  have hlow := rhinLite_pointwise_lower p q r t hn hsm
  obtain ⟨hBpos, _, hBle, _⟩ := rhinLiteFD_spec t
  have hBenv : (rhinLiteB t : ℝ) ≤ C * H ^ κ := le_trans hBle (henvt t ht₀ htle)
  have hBRpos : (0 : ℝ) < (rhinLiteB t : ℝ) := by exact_mod_cast hBpos
  have hHκpos : (0 : ℝ) < H ^ κ := by positivity
  calc (1 / (2 * C)) / H ^ κ = 1 / (2 * C * H ^ κ) := by rw [div_div]
    _ ≤ 1 / (2 * (rhinLiteB t : ℝ)) := by
        apply one_div_le_one_div_of_le (by linarith [hBRpos])
        nlinarith [hBenv]
    _ ≤ |(p : ℝ) + q * Real.log (3 / 2) + r * Real.log (4 / 3)| := hlow

/-- **The explicit Rhin-lite constant** `c = 1 / (2·(396/5)^6000·6^436)` (`log₂(1/c) ≈ 38972`). -/
noncomputable def rhinLiteSepC : ℝ := 1 / (2 * ((396 / 5 : ℝ) ^ 6000 * 6 ^ 436))

theorem rhinLiteSepC_pos : 0 < rhinLiteSepC := by unfold rhinLiteSepC; positivity

/-- **The Rhin-lite linear-independence measure with explicit constants**: exponent `436`,
constant `rhinLiteSepC`.  No `sorry`, no literature axiom. -/
theorem rhinLiteLIMeasure_explicit (p q r : ℤ) (h : p ≠ 0 ∨ q ≠ 0 ∨ r ≠ 0) :
    rhinLiteSepC / (max |(p : ℝ)| (max |(q : ℝ)| |(r : ℝ)|)) ^ 436
      ≤ |(p : ℝ) + q * Real.log (3 / 2) + r * Real.log (4 / 3)| :=
  rhinLiteLIMeasure_of_envelope 436 _ (by positivity)
    (rhinLite_selection_envelope_of_majorant 436 log_396_5_le_436 lcmUpto_even_le_pow) p q r h

/-! ### Transfer to the Baker linear form on the near-critical window -/

/-- **Effective measure of `log₂3` from Rhin-lite (explicit).**  On the near-critical window
`3^k < 2^m < 2·3^k` (`k ≥ 1`): `rhinLiteSepC / k^436 ≤ m·log2 − k·log3`.  The form is
`(m−2k)·log(3/2) + (m−k)·log(4/3)` (`linForm_eq_log23`), of height `≤ k` since `k < m ≤ 2k`. -/
theorem rhinLite_log23_measure (k m : ℕ) (hk : 1 ≤ k) (h1 : 3 ^ k < 2 ^ m)
    (h2 : 2 ^ m < 2 * 3 ^ k) :
    rhinLiteSepC / (k : ℝ) ^ 436 ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
  have hkm : k < m := by
    have h2k : (2 : ℕ) ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
    have : (2 : ℕ) ^ k < 2 ^ m := lt_of_le_of_lt h2k h1
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hm2k : m ≤ 2 * k := by
    have hbnd : 2 * 3 ^ k ≤ 2 ^ (2 * k + 1) := by
      calc 2 * 3 ^ k ≤ 2 * 4 ^ k := by gcongr; norm_num
        _ = 2 ^ (2 * k + 1) := by
            rw [pow_succ, pow_mul]; norm_num; ring
    have : (2 : ℕ) ^ m < 2 ^ (2 * k + 1) := lt_of_lt_of_le h2 hbnd
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    omega
  have hΛpos : (0 : ℝ) < (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
    have h3lt : (3 : ℝ) ^ k < (2 : ℝ) ^ m := by exact_mod_cast h1
    have hlog : Real.log ((3 : ℝ) ^ k) < Real.log ((2 : ℝ) ^ m) :=
      Real.log_lt_log (by positivity) h3lt
    rw [Real.log_pow, Real.log_pow] at hlog
    linarith
  have hr0 : ((m : ℤ) - k : ℤ) ≠ 0 := by omega
  have hmeas := rhinLiteLIMeasure_explicit 0 ((m : ℤ) - 2 * k) ((m : ℤ) - k)
    (Or.inr (Or.inr hr0))
  have hform : (((0 : ℤ)) : ℝ) + (((m : ℤ) - 2 * k : ℤ) : ℝ) * Real.log (3 / 2)
      + (((m : ℤ) - k : ℤ) : ℝ) * Real.log (4 / 3)
      = (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
    have := linForm_eq_log23 (k : ℝ) (m : ℝ)
    push_cast
    linarith [this]
  rw [hform, abs_of_pos hΛpos] at hmeas
  set Hh : ℝ := max |(((0 : ℤ)) : ℝ)|
    (max |(((m : ℤ) - 2 * k : ℤ) : ℝ)| |(((m : ℤ) - k : ℤ) : ℝ)|) with hHhdef
  have hkR : (k : ℝ) ≤ m := by exact_mod_cast hkm.le
  have hmR : (m : ℝ) ≤ 2 * k := by exact_mod_cast hm2k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hHle : Hh ≤ k := by
    rw [hHhdef]
    apply max_le
    · simp
    apply max_le
    · push_cast; rw [abs_le]; constructor <;> linarith
    · push_cast; rw [abs_le]; constructor <;> linarith
  have hHpos : 0 < Hh := by
    have h1' : (1 : ℝ) ≤ |(((m : ℤ) - k : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hr0
    have : |(((m : ℤ) - k : ℤ) : ℝ)| ≤ Hh :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  calc rhinLiteSepC / (k : ℝ) ^ 436 ≤ rhinLiteSepC / Hh ^ 436 := by
        apply div_le_div_of_nonneg_left rhinLiteSepC_pos.le (pow_pos hHpos _)
        exact pow_le_pow_left₀ hHpos.le hHle _
    _ ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := hmeas

/-! ### The crossover -/

/-- **Generic crossover by induction.**  If `K^κ ≤ c·2^(K/3)` and `5κ ≤ K`, then
`k^κ ≤ c·2^(k/3)` for all `k ≥ K` (ratio step `((n+1)/n)^κ ≤ exp(κ/n) ≤ 2^(1/3)`). -/
theorem crossover_exp_of_base (c : ℝ) (κ K : ℕ) (hK : 5 * κ ≤ K) (hKpos : 0 < K)
    (hbase : (K : ℝ) ^ κ ≤ c * Real.exp ((K : ℝ) / 3 * Real.log 2)) :
    ∀ k : ℕ, K ≤ k → (k : ℝ) ^ κ ≤ c * Real.exp ((k : ℝ) / 3 * Real.log 2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
      have hnpos : 0 < n := lt_of_lt_of_le hKpos hn
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hbase' : (1 + 1 / (n : ℝ)) ≤ Real.exp (1 / (n : ℝ)) := by
        have := Real.add_one_le_exp (1 / (n : ℝ)); linarith
      have h0 : (0 : ℝ) ≤ 1 + 1 / (n : ℝ) := by positivity
      have hpow : (1 + 1 / (n : ℝ)) ^ κ ≤ (Real.exp (1 / (n : ℝ))) ^ κ :=
        pow_le_pow_left₀ h0 hbase' κ
      have hexp : (Real.exp (1 / (n : ℝ))) ^ κ = Real.exp ((κ : ℝ) / n) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      have hCn : (κ : ℝ) / n ≤ (1 / 3) * Real.log 2 := by
        have hnge : (5 * κ : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hK hn
        have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        rw [div_le_iff₀ hnR]
        nlinarith [hlog, hnge, Nat.cast_nonneg (α := ℝ) κ]
      have hexple : Real.exp ((κ : ℝ) / n) ≤ Real.exp ((1 / 3) * Real.log 2) :=
        Real.exp_le_exp.mpr hCn
      have hratiobound : (1 + 1 / (n : ℝ)) ^ κ ≤ Real.exp ((1 / 3) * Real.log 2) := by
        calc (1 + 1 / (n : ℝ)) ^ κ ≤ Real.exp ((κ : ℝ) / n) := by rw [← hexp]; exact hpow
          _ ≤ Real.exp ((1 / 3) * Real.log 2) := hexple
      have hsplit : Real.exp (((n + 1 : ℕ) : ℝ) / 3 * Real.log 2)
          = Real.exp (((n : ℕ) : ℝ) / 3 * Real.log 2) * Real.exp ((1 / 3) * Real.log 2) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have hnκ : ((n + 1 : ℕ) : ℝ) ^ κ = (n : ℝ) ^ κ * (1 + 1 / (n : ℝ)) ^ κ := by
        have hne : (n : ℝ) ≠ 0 := ne_of_gt hnR
        have hnn1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) * (1 + 1 / (n : ℝ)) := by
          push_cast; field_simp
        rw [hnn1, mul_pow]
      rw [hsplit, hnκ]
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ κ := by positivity
      have hexppos : (0 : ℝ) < Real.exp ((1 / 3) * Real.log 2) := Real.exp_pos _
      calc (n : ℝ) ^ κ * (1 + 1 / (n : ℝ)) ^ κ
          ≤ (n : ℝ) ^ κ * Real.exp ((1 / 3) * Real.log 2) :=
            mul_le_mul_of_nonneg_left hratiobound hnn
        _ ≤ (c * Real.exp (((n : ℕ) : ℝ) / 3 * Real.log 2)) * Real.exp ((1 / 3) * Real.log 2) :=
            mul_le_mul_of_nonneg_right ih hexppos.le
        _ = c * (Real.exp (((n : ℕ) : ℝ) / 3 * Real.log 2) * Real.exp ((1 / 3) * Real.log 2)) := by
            ring

/-- Base case of the crossover at `K = 141000 = 3·47000`, as a kernel-checked natural-number
inequality (`≈ 14000`-digit operands, margin `≈ 133` bits). -/
theorem crossover_base_141000_nat :
    2 * 141000 ^ 436 * 396 ^ 6000 * 6 ^ 436 ≤ 2 ^ 47000 * 5 ^ 6000 := by
  decide +kernel

/-- **Concrete crossover for the Rhin-lite measure**: `k^436 ≤ rhinLiteSepC · 2^(k/3)` for
`k ≥ 141000`. -/
theorem crossover_exp_436_141000 (k : ℕ) (hk : 141000 ≤ k) :
    (k : ℝ) ^ 436 ≤ rhinLiteSepC * Real.exp ((k : ℝ) / 3 * Real.log 2) := by
  refine crossover_exp_of_base rhinLiteSepC 436 141000 (by norm_num) (by norm_num) ?_ k hk
  have he : Real.exp (((141000 : ℕ) : ℝ) / 3 * Real.log 2) = (2 : ℝ) ^ 47000 := by
    have hlg : ((141000 : ℕ) : ℝ) / 3 * Real.log 2 = Real.log ((2 : ℝ) ^ 47000) := by
      rw [Real.log_pow]; push_cast; ring
    rw [hlg, Real.exp_log (by positivity)]
  rw [he]
  unfold rhinLiteSepC
  have hR : (2 : ℝ) * 141000 ^ 436 * 396 ^ 6000 * 6 ^ 436 ≤ 2 ^ 47000 * 5 ^ 6000 := by
    exact_mod_cast crossover_base_141000_nat
  have h5 : (0 : ℝ) < 5 ^ 6000 := by positivity
  have h396 : (396 / 5 : ℝ) ^ 6000 = 396 ^ 6000 / 5 ^ 6000 := div_pow _ _ _
  rw [h396]
  push_cast
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  have : ((141000 : ℝ) ^ 436) * (2 * (396 ^ 6000 / 5 ^ 6000 * 6 ^ 436)) * 5 ^ 6000
      = 2 * 141000 ^ 436 * 396 ^ 6000 * 6 ^ 436 := by
    field_simp
  nlinarith [this, hR, h5]

/-! ### The finite range through convergent brackets of `log₂3` -/

/-- **Per-`k` separation from a convergent bracket, all-integer hypotheses.**  A unimodular bracket
`a/b < θ < c/d` (`θ = log₂3`, `b·c = a·d + 1`) straddling `k` (`k < b + d`), with inner fractions
`a/b < a'/b' < θ < c'/d' < c/d` and a scale `j` with `3j ≤ k`, `2b' ≤ 2^j`, `2d' ≤ 2^j`, gives
`3^(3k) ≤ (2^m − 3^k)^3·2^k`.  The gap `min(bθ−a, c−dθ) ≥ min(1/b', 1/d')` comes from the inner
fractions; the required `2^(−k/3) ≤ log2·gap` is then the integer condition on `j`. -/
theorem sep_of_bracket_nat (k m a b c d a' b' c' d' j : ℕ) (hk : 0 < k)
    (h1 : 3 ^ k < 2 ^ m) (hb : 0 < b) (hd : 0 < d) (hb' : 0 < b') (hd' : 0 < d')
    (huni : b * c = a * d + 1)
    (hlo : 2 ^ a < 3 ^ b) (hhi : 3 ^ d < 2 ^ c)
    (hlo' : 2 ^ a' < 3 ^ b') (hhi' : 3 ^ d' < 2 ^ c')
    (hin1 : a * b' < a' * b) (hin2 : c' * d < c * d')
    (hklt : k < b + d) (hjk : 3 * j ≤ k) (hg1 : 2 * b' ≤ 2 ^ j) (hg2 : 2 * d' ≤ 2 ^ j) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  set θ := Real.logb 2 3 with hθ
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hb'R : (0 : ℝ) < b' := by exact_mod_cast hb'
  have hd'R : (0 : ℝ) < d' := by exact_mod_cast hd'
  have hloR : (a : ℝ) / b < θ := (lt_logb_two_three_iff a b hb).mpr hlo
  have hhiR : θ < (c : ℝ) / d := (logb_two_three_lt_iff c d hd).mpr hhi
  have hlo'R : (a' : ℝ) / b' < θ := (lt_logb_two_three_iff a' b' hb').mpr hlo'
  have hhi'R : θ < (c' : ℝ) / d' := (logb_two_three_lt_iff c' d' hd').mpr hhi'
  -- bθ − a ≥ 1/b'
  have hgap1 : (1 : ℝ) / b' ≤ (b : ℝ) * θ - a := by
    have ha' : (a' : ℝ) < θ * b' := by rwa [div_lt_iff₀ hb'R] at hlo'R
    have h1' : (a : ℝ) * b' + 1 ≤ a' * b := by
      have : a * b' + 1 ≤ a' * b := hin1
      exact_mod_cast this
    have hmul : (b : ℝ) * a' < b * (θ * b') := mul_lt_mul_of_pos_left ha' hbR
    rw [div_le_iff₀ hb'R]
    nlinarith
  -- c − dθ ≥ 1/d'
  have hgap2 : (1 : ℝ) / d' ≤ (c : ℝ) - d * θ := by
    have hc' : θ * d' < c' := by rwa [lt_div_iff₀ hd'R] at hhi'R
    have h2' : (c' : ℝ) * d + 1 ≤ c * d' := by
      have : c' * d + 1 ≤ c * d' := hin2
      exact_mod_cast this
    have hmul : (d : ℝ) * (θ * d') < d * c' := mul_lt_mul_of_pos_left hc' hdR
    rw [div_le_iff₀ hd'R]
    nlinarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hg1R : (2 : ℝ) * b' ≤ 2 ^ j := by exact_mod_cast hg1
  have hg2R : (2 : ℝ) * d' ≤ 2 ^ j := by exact_mod_cast hg2
  have hA : (1 : ℝ) / 2 ^ j ≤ 1 / (2 * b') := one_div_le_one_div_of_le (by positivity) hg1R
  have hB : (1 : ℝ) / 2 ^ j ≤ 1 / (2 * d') := one_div_le_one_div_of_le (by positivity) hg2R
  have hmin : (1 : ℝ) / 2 ^ j ≤ Real.log 2 * min ((b : ℝ) * θ - a) ((c : ℝ) - d * θ) := by
    rw [mul_min_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ Real.log 2)]
    apply le_min
    · calc (1 : ℝ) / 2 ^ j ≤ 1 / (2 * b') := hA
        _ = (1 / 2) * (1 / b') := by rw [one_div_mul_one_div]
        _ ≤ Real.log 2 * ((b : ℝ) * θ - a) :=
            mul_le_mul hlog2 hgap1 (by positivity) (by linarith)
    · calc (1 : ℝ) / 2 ^ j ≤ 1 / (2 * d') := hB
        _ = (1 / 2) * (1 / d') := by rw [one_div_mul_one_div]
        _ ≤ Real.log 2 * ((c : ℝ) - d * θ) :=
            mul_le_mul hlog2 hgap2 (by positivity) (by linarith)
  have hexp : Real.exp (-(k : ℝ) / 3 * Real.log 2) ≤ (1 : ℝ) / 2 ^ j := by
    have hjk' : (j : ℝ) ≤ (k : ℝ) / 3 := by
      have : (3 * j : ℝ) ≤ k := by exact_mod_cast hjk
      linarith
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hle : -(k : ℝ) / 3 * Real.log 2 ≤ -(j : ℝ) * Real.log 2 := by nlinarith
    calc Real.exp (-(k : ℝ) / 3 * Real.log 2) ≤ Real.exp (-(j : ℝ) * Real.log 2) :=
          Real.exp_le_exp.mpr hle
      _ = 1 / 2 ^ j := by
          rw [show -(j : ℝ) * Real.log 2 = -(Real.log ((2 : ℝ) ^ j)) by
                rw [Real.log_pow]; ring,
              Real.exp_neg, Real.exp_log (by positivity), one_div]
  exact sep_of_bracket_sharp k m a b c d hk h1 hb hd huni hloR hhiR hklt (le_trans hexp hmin)

/-! Integer power certificates for the convergents of `log₂3` (all kernel-checked):
convergents `485/306 (>)`, `1054/665 (<)`, `24727/15601 (>)`, `50508/31867 (<)`, `125743/79335 (>)`,
`176251/111202 (<)`, `301994/190537 (>)`, and the semiconvergent `478245/301739 (<)`. -/

theorem pow_cert_306 : 3 ^ 306 < 2 ^ 485 := by decide +kernel
theorem pow_cert_665 : 2 ^ 1054 < 3 ^ 665 := by decide +kernel
theorem pow_cert_15601 : 3 ^ 15601 < 2 ^ 24727 := by decide +kernel
theorem pow_cert_31867 : 2 ^ 50508 < 3 ^ 31867 := by decide +kernel
theorem pow_cert_79335 : 3 ^ 79335 < 2 ^ 125743 := by decide +kernel
theorem pow_cert_111202 : 2 ^ 176251 < 3 ^ 111202 := by decide +kernel
theorem pow_cert_190537 : 3 ^ 190537 < 2 ^ 301994 := by decide +kernel
theorem pow_cert_301739 : 2 ^ 478245 < 3 ^ 301739 := by decide +kernel

/-- **Finite range `6 ≤ k < 141000`.**  `k < 450`: the table `sep_two_three_small_450`.
`450 ≤ k < 141000`: five consecutive-convergent brackets, each covering `[q_{n-1}+q_n, q_n+q_{n+1})`
with the next same-side fractions as inner gap witnesses. -/
theorem sep_two_three_finite_141000 (k m : ℕ) (hk : 6 ≤ k) (hklt : k < 141000)
    (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  rcases lt_or_ge k 450 with h450 | h450
  · exact sep_two_three_small_450 k m hk h450 h1 h2
  rcases lt_or_ge k 971 with hA | hA
  · -- bracket (665, 306): 1054/665 < θ < 485/306; inner 50508/31867, 24727/15601; j = 150
    exact sep_of_bracket_nat k m 1054 665 485 306 50508 31867 24727 15601 150 (by omega) h1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      pow_cert_665 pow_cert_306 pow_cert_31867 pow_cert_15601
      (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
  rcases lt_or_ge k 16266 with hB | hB
  · -- bracket (665, 15601): 1054/665 < θ < 24727/15601; inner 50508/31867, 125743/79335; j = 323
    exact sep_of_bracket_nat k m 1054 665 24727 15601 50508 31867 125743 79335 323 (by omega) h1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      pow_cert_665 pow_cert_15601 pow_cert_31867 pow_cert_79335
      (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
  rcases lt_or_ge k 47468 with hC | hC
  · -- bracket (31867, 15601): 50508/31867 < θ < 24727/15601; inner 176251/111202, 125743/79335
    exact sep_of_bracket_nat k m 50508 31867 24727 15601 176251 111202 125743 79335 5422
      (by omega) h1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      pow_cert_31867 pow_cert_15601 pow_cert_111202 pow_cert_79335
      (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
  rcases lt_or_ge k 111202 with hD | hD
  · -- bracket (31867, 79335): 50508/31867 < θ < 125743/79335; inner 176251/111202, 301994/190537
    exact sep_of_bracket_nat k m 50508 31867 125743 79335 176251 111202 301994 190537 15822
      (by omega) h1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      pow_cert_31867 pow_cert_79335 pow_cert_111202 pow_cert_190537
      (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)
  · -- bracket (111202, 79335): 176251/111202 < θ < 125743/79335; inner 478245/301739, 301994/190537
    exact sep_of_bracket_nat k m 176251 111202 125743 79335 478245 301739 301994 190537 37067
      (by omega) h1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      pow_cert_111202 pow_cert_79335 pow_cert_301739 pow_cert_190537
      (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num) (by norm_num)

/-! ### The re-wired separation theorem -/

/-- **`sep_two_three` from the Rhin-lite measure (no literature axiom).**  Instantiates
`sep_of_linear_form_poly_threshold` at `c = rhinLiteSepC`, `κ = 436`, `K = 141000` with the
explicit measure `rhinLite_log23_measure`, the crossover `crossover_exp_436_141000`, and the
finite range `sep_two_three_finite_141000`. -/
theorem sep_two_three_rhinLite (k m : ℕ) (hk : 6 ≤ k) (h1 : 3 ^ k < 2 ^ m)
    (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k :=
  sep_of_linear_form_poly_threshold rhinLiteSepC 436 141000
    (fun k m hk h1 h2 => rhinLite_log23_measure k m (by omega) h1 h2)
    crossover_exp_436_141000 sep_two_three_finite_141000 k m hk h1 h2

/-- **Weak power separation `β = 1/3` — PROVED, no literature axiom.**  For the near-critical
power `2^m` just above `3^k` (`3^k < 2^m < 2·3^k`) with `k ≥ 6`, `3^(3k) ≤ (2^m − 3^k)^3 · 2^k`,
i.e. `2^m − 3^k ≥ 3^k · 2^(−k/3)`.  This is the sink node of the two-block exclusion
(`bd_reduction` below, `le_two_blocks_not_acyclicParadoxical` in `Paradoxical.lean`).  It is
`sep_two_three_rhinLite`; its ledger is the trust base plus the `native_decide` certificates of the
Rhin-lite tower — the cited Rhin 1987 axiom is no longer used (parked in `wip/RhinAxiomRoute.lean`). -/
theorem sep_two_three (k m : ℕ) (hk : 6 ≤ k) (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k :=
  sep_two_three_rhinLite k m hk h1 h2

/-- **The reduction (machine-checked modulo `sep_two_three`).**  Given the near-critical window
`3^k < 2^m < 2·3^k` and the two block inequalities
  `(W) : 2^d·(2^m − 3^k) < 2^m`  and  `(A) : (2^m − 3^k)·2^k ≤ 2^m·3^d`,
with `1 ≤ d < k`, the separation forces `k ≤ 5`.  (β=1/3 gives the elementary bound `k ≤ 14` via
`grow_two_three`; the residue `6 ≤ k ≤ 14` is cleared by `finite_two_block_check`.) -/
theorem bd_reduction (k m d : ℕ) (hk1 : 1 ≤ d) (hdk : d < k)
    (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k)
    (hW : 2 ^ d * (2 ^ m - 3 ^ k) < 2 ^ m)
    (hA : (2 ^ m - 3 ^ k) * 2 ^ k ≤ 2 ^ m * 3 ^ d) :
    k ≤ 5 := by
  by_contra hcon
  have hk6 : 6 ≤ k := by omega
  set D := 2 ^ m - 3 ^ k with hD
  have hDpos : 0 < D := by rw [hD]; omega
  have hS : 3 ^ (3 * k) ≤ D ^ 3 * 2 ^ k := sep_two_three k m hk6 h1 h2
  have hD3 : 0 < D ^ 3 := by positivity
  -- (ii'): 3d < k+3
  have hii : 3 * d < k + 3 := by
    have hWc : (2 ^ d * D) ^ 3 < (2 * 3 ^ k) ^ 3 := by
      apply Nat.pow_lt_pow_left _ (by norm_num)
      calc 2 ^ d * D < 2 ^ m := hW
        _ < 2 * 3 ^ k := h2
    have key : D ^ 3 * (2 ^ d) ^ 3 < D ^ 3 * 2 ^ (k + 3) := by
      calc D ^ 3 * (2 ^ d) ^ 3 = (2 ^ d * D) ^ 3 := by ring
        _ < (2 * 3 ^ k) ^ 3 := hWc
        _ = 8 * 3 ^ (3 * k) := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 3]; norm_num
        _ ≤ 8 * (D ^ 3 * 2 ^ k) := by gcongr
        _ = D ^ 3 * 2 ^ (k + 3) := by rw [pow_add]; ring
    have hpow : (2 ^ d) ^ 3 < 2 ^ (k + 3) := Nat.lt_of_mul_lt_mul_left key
    rw [← pow_mul] at hpow
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp hpow
    omega
  -- (iii'): 2^(2k-3) < 3^(3d)
  have hiii : 2 ^ (2 * k - 3) < 3 ^ (3 * d) := by
    have hAstrict : D * 2 ^ k < 2 * 3 ^ (k + d) := by
      calc D * 2 ^ k ≤ 2 ^ m * 3 ^ d := hA
        _ < 2 * 3 ^ k * 3 ^ d := by gcongr
        _ = 2 * 3 ^ (k + d) := by rw [pow_add]; ring
    have hAc : (D * 2 ^ k) ^ 3 < (2 * 3 ^ (k + d)) ^ 3 :=
      Nat.pow_lt_pow_left hAstrict (by norm_num)
    have hlow : 3 ^ (3 * k) * 2 ^ (2 * k) ≤ (D * 2 ^ k) ^ 3 := by
      calc 3 ^ (3 * k) * 2 ^ (2 * k) ≤ (D ^ 3 * 2 ^ k) * 2 ^ (2 * k) := by gcongr
        _ = D ^ 3 * 2 ^ (3 * k) := by
              rw [mul_assoc, ← pow_add, show k + 2 * k = 3 * k by ring]
        _ = (D * 2 ^ k) ^ 3 := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 3]
    have hchain : 3 ^ (3 * k) * 2 ^ (2 * k) < (2 * 3 ^ (k + d)) ^ 3 := lt_of_le_of_lt hlow hAc
    have hRHS : (2 * 3 ^ (k + d)) ^ 3 = 3 ^ (3 * k) * (8 * 3 ^ (3 * d)) := by
      rw [mul_pow, ← pow_mul, show (k + d) * 3 = 3 * k + 3 * d by ring, pow_add]; ring
    rw [hRHS] at hchain
    have hcancel : 2 ^ (2 * k) < 8 * 3 ^ (3 * d) := Nat.lt_of_mul_lt_mul_left hchain
    have hsplit : 2 ^ (2 * k) = 2 ^ (2 * k - 3) * 8 := by
      rw [show (8:ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega
    rw [hsplit] at hcancel
    have hmul : 2 ^ (2 * k - 3) * 8 < 3 ^ (3 * d) * 8 := by omega
    exact Nat.lt_of_mul_lt_mul_right hmul
  -- combine (ii') + (iii'): 2^(2k-3) < 3^(k+2)
  have hd3 : 3 * d ≤ k + 2 := by omega
  have h3dle : 3 ^ (3 * d) ≤ 3 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) hd3
  have hiv : 2 ^ (2 * k - 3) < 3 ^ (k + 2) := lt_of_lt_of_le hiii h3dle
  by_cases hk15 : 15 ≤ k
  · exact absurd (grow_two_three k hk15) (by omega)
  · have hkle : k ≤ 14 := by omega
    have hmlt : m < 24 := by
      have hlt : 2 ^ m < 2 ^ 24 := by
        calc 2 ^ m < 2 * 3 ^ k := h2
          _ ≤ 2 * 3 ^ 14 := by gcongr <;> norm_num
          _ < 2 ^ 24 := by norm_num
      exact (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp hlt
    exact finite_two_block_check k (Finset.mem_range.mpr (by omega)) m
      (Finset.mem_range.mpr hmlt) d (Finset.mem_range.mpr (by omega))
      ⟨hk6, hk1, hdk, h1, h2, hW, hA⟩


end CollatzMoonshot.FrontA
