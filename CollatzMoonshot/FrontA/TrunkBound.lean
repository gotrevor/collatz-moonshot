/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.Excursion
import CollatzMoonshot.FrontA.RhinLiteSep

/-!
# The min-term trunk bound: every paradoxical segment dips below `a/(3Λ)`

This is the **easy (min-term) half of Rozier–Terracol, Theorem 4.2** (harmonic-mean
form), written out for the repository's shortcut map `tstep` and its parity trace.
No novelty is claimed.  Its value is the exact trajectory-side foothold that
`DIRECTION.md` names: every paradoxical segment, odd or even start, cyclic or strict
endpoint, contains an odd-step value below `a / (3·(m·log 2 − a·log 3))`.

Write `x_i = tstep^[i] n`, `I = {i < m | x_i odd}` (`oddSteps`), `a = |I| = ones (traceWord n m)`.

1. **Product identity** (`tstep_iterate_prod_identity`):
   `2^m · x_m · ∏_{i∈I} 3x_i = 3^a · n · ∏_{i∈I} (3x_i + 1)`.
   Each odd step is `x ↦ (3x+1)/2 = (3/2)·x·(1 + 1/(3x))`; each even step is `x ↦ x/2`.
   Induction on `m` with the new index appended at the end of `Finset.range`.
2. **Min-term inequality** (`min_term_inequality`): if `0 < m` and `n < x_m`, then for every
   lower bound `1 ≤ x ≤ x_i` (`i ∈ I`), `2^m · (3x)^a < 3^a · (3x+1)^a`, since each factor
   `(3x_i+1)/(3x_i)` is at most `(3x+1)/(3x)`.  Endpoint equality (`n ≤ x_m`) gives `≤`
   (`min_term_inequality_le`), so the cyclic case is retained.
3. **Real form** (`segMin_lt_of_subcritical`): with `3^a < 2^m` and `Λ = m·log 2 − a·log 3 > 0`,
   `x_min < a / (3Λ)`, via `log(1+t) ≤ t` applied to the ratio.
4. **Rhin-lite corollary** (`segMin_lt_poly_of_acyclicParadoxical`): on the near-critical window
   the explicit measure `rhinLite_log23_measure` gives `Λ ≥ rhinLiteSepC / a^436`, and off the
   window `Λ ≥ log 2`; so `x_min < a^437 / (3·rhinLiteSepC) + a`.  **Trust ledger:** (1)–(3) are
   standard trust triple only; (4) inherits the eleven explicitly allow-listed Rhin-lite
   `native_decide` certificates through `rhinLite_log23_measure`, exactly like the existing
   fixed-run length theorem, and is therefore a separate declaration.

Kernel control on `(7, 8)`: odd-step values `7, 11, 17, 13, 5`, `x_min = 5`, `a = 5`, and
`3^5 · 16^5 = 254803968 > 194400000 = 2^8 · 15^5` (`trunkBound_control_seven_eight`).
-/

namespace CollatzMoonshot.FrontA

open CollatzMoonshot CollatzMoonshot.FrontB Finset

/-- The odd-step indices of the first `m` shortcut steps from `n`. -/
def oddSteps (n m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun i => tstep^[i] n % 2 = 1)

theorem oddSteps_zero (n : ℕ) : oddSteps n 0 = ∅ := by
  simp [oddSteps]

theorem oddSteps_succ (n m : ℕ) :
    oddSteps n (m + 1) =
      if tstep^[m] n % 2 = 1 then insert m (oddSteps n m) else oddSteps n m := by
  unfold oddSteps
  rw [Finset.range_add_one, Finset.filter_insert]

theorem not_mem_oddSteps_self (n m : ℕ) : m ∉ oddSteps n m := by
  simp [oddSteps]

theorem mem_oddSteps {n m i : ℕ} : i ∈ oddSteps n m ↔ i < m ∧ tstep^[i] n % 2 = 1 := by
  simp [oddSteps]

/-- Odd-step values are odd, hence positive. -/
theorem one_le_of_mem_oddSteps {n m i : ℕ} (hi : i ∈ oddSteps n m) : 1 ≤ tstep^[i] n := by
  have := (mem_oddSteps.mp hi).2
  omega

/-- The odd-step count of the trace is the size of the odd-step set. -/
theorem card_oddSteps (n m : ℕ) : (oddSteps n m).card = ones (traceWord n m) := by
  induction m with
  | zero => simp [oddSteps, traceWord]
  | succ k ih =>
    rw [oddSteps_succ, traceWord_add, ones_append]
    have h1 : ones (traceWord (tstep^[k] n) 1) = if tstep^[k] n % 2 = 1 then 1 else 0 := by
      simp only [traceWord]
      split_ifs with h <;> simp [h, ones]
    rw [h1]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (not_mem_oddSteps_self n k), ih]
    · rw [ih, Nat.add_zero]

/-- **Product identity.** `2^m · x_m · ∏_{i∈I} 3x_i = 3^a · n · ∏_{i∈I} (3x_i+1)`, i.e.
`x_m / n = (3^a / 2^m) · ∏_{i∈I} (1 + 1/(3x_i))`. -/
theorem tstep_iterate_prod_identity (n m : ℕ) :
    2 ^ m * tstep^[m] n * ∏ i ∈ oddSteps n m, (3 * tstep^[i] n) =
      3 ^ ones (traceWord n m) * n * ∏ i ∈ oddSteps n m, (3 * tstep^[i] n + 1) := by
  induction m with
  | zero => simp [oddSteps, traceWord]
  | succ k ih =>
    rw [oddSteps_succ, traceWord_add, ones_append]
    have h1 : ones (traceWord (tstep^[k] n) 1) = if tstep^[k] n % 2 = 1 then 1 else 0 := by
      simp only [traceWord]
      split_ifs with h <;> simp [h, ones]
    rw [h1, Function.iterate_succ_apply']
    set X := tstep^[k] n with hX
    set P := ∏ i ∈ oddSteps n k, (3 * tstep^[i] n) with hP
    set Q := ∏ i ∈ oddSteps n k, (3 * tstep^[i] n + 1) with hQ
    set a := ones (traceWord n k) with ha
    split_ifs with h
    · -- odd step: `2 · tstep X = 3X + 1`
      have h2 : 2 * tstep X = 3 * X + 1 := by
        unfold tstep; split <;> omega
      rw [Finset.prod_insert (not_mem_oddSteps_self n k),
        Finset.prod_insert (not_mem_oddSteps_self n k)]
      rw [← hX, ← hP, ← hQ]
      calc 2 ^ (k + 1) * tstep X * (3 * X * P)
          = 2 ^ k * (2 * tstep X) * (3 * X * P) := by ring
        _ = 2 ^ k * (3 * X + 1) * (3 * X * P) := by rw [h2]
        _ = (2 ^ k * X * P) * (3 * (3 * X + 1)) := by ring
        _ = (3 ^ a * n * Q) * (3 * (3 * X + 1)) := by rw [ih]
        _ = 3 ^ (a + 1) * n * ((3 * X + 1) * Q) := by ring
    · -- even step: `2 · tstep X = X`
      have h2 : 2 * tstep X = X := by
        unfold tstep; split <;> omega
      rw [← hP, ← hQ, Nat.add_zero]
      calc 2 ^ (k + 1) * tstep X * P
          = 2 ^ k * (2 * tstep X) * P := by ring
        _ = 2 ^ k * X * P := by rw [h2]
        _ = 3 ^ a * n * Q := ih

/-- Positivity of the odd-value product. -/
theorem prod_oddSteps_pos (n m : ℕ) : 0 < ∏ i ∈ oddSteps n m, (3 * tstep^[i] n) :=
  Finset.prod_pos fun i hi => by have := one_le_of_mem_oddSteps hi; omega

/-- **Factor comparison.**  For a lower bound `x ≤ x_i` on the odd-step values,
`∏ (3x_i+1) · (3x)^a ≤ (3x+1)^a · ∏ 3x_i`. -/
theorem prod_ratio_le (n m x : ℕ) (hx : ∀ i ∈ oddSteps n m, x ≤ tstep^[i] n) :
    (∏ i ∈ oddSteps n m, (3 * tstep^[i] n + 1)) * (3 * x) ^ (oddSteps n m).card ≤
      (3 * x + 1) ^ (oddSteps n m).card * ∏ i ∈ oddSteps n m, (3 * tstep^[i] n) := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun i _ => by positivity)
  intro i hi
  have := hx i hi
  nlinarith

/-- **Min-term inequality (weak form).**  If the endpoint does not fall below the start
(`n ≤ x_m`, so cyclic endpoints are retained), every lower bound `x` of the odd-step values
satisfies `2^m · (3x)^a ≤ 3^a · (3x+1)^a`. -/
theorem min_term_inequality_le (n m x : ℕ) (hn : 1 ≤ n) (hend : n ≤ tstep^[m] n)
    (hx : ∀ i ∈ oddSteps n m, x ≤ tstep^[i] n) :
    2 ^ m * (3 * x) ^ ones (traceWord n m) ≤
      3 ^ ones (traceWord n m) * (3 * x + 1) ^ ones (traceWord n m) := by
  have hid := tstep_iterate_prod_identity n m
  have hP := prod_oddSteps_pos n m
  have hr := prod_ratio_le n m x hx
  rw [card_oddSteps] at hr
  set P := ∏ i ∈ oddSteps n m, (3 * tstep^[i] n)
  set Q := ∏ i ∈ oddSteps n m, (3 * tstep^[i] n + 1)
  set a := ones (traceWord n m)
  -- `2^m · n · P ≤ 2^m · x_m · P = 3^a · n · Q`, cancel `n`.
  have h1 : 2 ^ m * P ≤ 3 ^ a * Q := by
    have : 2 ^ m * P * n ≤ 3 ^ a * Q * n := by
      calc 2 ^ m * P * n ≤ 2 ^ m * P * tstep^[m] n := by gcongr
        _ = 3 ^ a * Q * n := by linarith [hid]
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have h2 : 2 ^ m * (3 * x) ^ a * P ≤ 3 ^ a * (3 * x + 1) ^ a * P := by
    calc 2 ^ m * (3 * x) ^ a * P = (2 ^ m * P) * (3 * x) ^ a := by ring
      _ ≤ (3 ^ a * Q) * (3 * x) ^ a := by gcongr
      _ = 3 ^ a * (Q * (3 * x) ^ a) := by ring
      _ ≤ 3 ^ a * ((3 * x + 1) ^ a * P) := by gcongr
      _ = 3 ^ a * (3 * x + 1) ^ a * P := by ring
  exact Nat.le_of_mul_le_mul_right h2 hP

/-- The odd-step count of a strictly climbing segment is positive: with `a = 0` the
identity reads `2^m · x_m = n`, incompatible with `n < x_m`. -/
theorem one_le_ones_of_lt (n m : ℕ) (hend : n < tstep^[m] n) :
    1 ≤ ones (traceWord n m) := by
  by_contra h
  have ha : ones (traceWord n m) = 0 := by omega
  have hI : oddSteps n m = ∅ := Finset.card_eq_zero.mp (by rw [card_oddSteps, ha])
  have hid := tstep_iterate_prod_identity n m
  rw [hI, ha] at hid
  simp only [Finset.prod_empty, pow_zero, mul_one, one_mul] at hid
  have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  nlinarith

/-- **Min-term inequality (strict form).**  If the segment strictly climbs (`n < x_m`),
every lower bound `x` of the odd-step values satisfies `2^m · (3x)^a < 3^a · (3x+1)^a`.
Holds for every acyclic paradoxical segment, odd or even start; no subcriticality is used. -/
theorem min_term_inequality (n m x : ℕ) (hend : n < tstep^[m] n)
    (hx : ∀ i ∈ oddSteps n m, x ≤ tstep^[i] n) :
    2 ^ m * (3 * x) ^ ones (traceWord n m) <
      3 ^ ones (traceWord n m) * (3 * x + 1) ^ ones (traceWord n m) := by
  have ha := one_le_ones_of_lt n m hend
  have hid := tstep_iterate_prod_identity n m
  have hP := prod_oddSteps_pos n m
  have hr := prod_ratio_le n m x hx
  rw [card_oddSteps] at hr
  set P := ∏ i ∈ oddSteps n m, (3 * tstep^[i] n)
  set Q := ∏ i ∈ oddSteps n m, (3 * tstep^[i] n + 1)
  set a := ones (traceWord n m)
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · subst hx0
    have : (3 * 0) ^ a = 0 := by
      rw [mul_zero]; exact zero_pow (by omega)
    rw [this, mul_zero]
    positivity
  have h1 : 2 ^ m * P < 3 ^ a * Q := by
    have : 2 ^ m * P * n < 3 ^ a * Q * n := by
      calc 2 ^ m * P * n < 2 ^ m * P * tstep^[m] n := by gcongr
        _ = 3 ^ a * Q * n := by linarith [hid]
    exact Nat.lt_of_mul_lt_mul_right this
  have hxpos : 0 < (3 * x) ^ a := by positivity
  have h2 : 2 ^ m * (3 * x) ^ a * P < 3 ^ a * (3 * x + 1) ^ a * P := by
    calc 2 ^ m * (3 * x) ^ a * P = (2 ^ m * P) * (3 * x) ^ a := by ring
      _ < (3 ^ a * Q) * (3 * x) ^ a := by gcongr
      _ = 3 ^ a * (Q * (3 * x) ^ a) := by ring
      _ ≤ 3 ^ a * ((3 * x + 1) ^ a * P) := by gcongr
      _ = 3 ^ a * (3 * x + 1) ^ a * P := by ring
  exact Nat.lt_of_mul_lt_mul_right h2

/-! ### The segment minimum over odd steps -/

/-- The least odd-step value of the first `m` shortcut steps from `n` (`0` if there is none). -/
def segMin (n m : ℕ) : ℕ :=
  if h : (oddSteps n m).Nonempty then (oddSteps n m).inf' h (fun i => tstep^[i] n) else 0

theorem segMin_le {n m i : ℕ} (hi : i ∈ oddSteps n m) : segMin n m ≤ tstep^[i] n := by
  unfold segMin
  rw [dif_pos ⟨i, hi⟩]
  exact Finset.inf'_le _ hi

theorem exists_segMin_eq {n m : ℕ} (h : (oddSteps n m).Nonempty) :
    ∃ i ∈ oddSteps n m, segMin n m = tstep^[i] n := by
  unfold segMin
  rw [dif_pos h]
  exact Finset.exists_mem_eq_inf' h _

theorem one_le_segMin {n m : ℕ} (h : (oddSteps n m).Nonempty) : 1 ≤ segMin n m := by
  obtain ⟨i, hi, he⟩ := exists_segMin_eq h
  rw [he]; exact one_le_of_mem_oddSteps hi

/-- A strictly climbing segment has an odd step. -/
theorem oddSteps_nonempty_of_lt (n m : ℕ) (hend : n < tstep^[m] n) : (oddSteps n m).Nonempty := by
  rw [← Finset.card_pos, card_oddSteps]
  exact one_le_ones_of_lt n m hend

/-- **Min-term inequality at the segment minimum.**  For a strictly climbing segment,
`2^m · (3·x_min)^a < 3^a · (3·x_min + 1)^a`. -/
theorem min_term_inequality_segMin (n m : ℕ) (hend : n < tstep^[m] n) :
    2 ^ m * (3 * segMin n m) ^ ones (traceWord n m) <
      3 ^ ones (traceWord n m) * (3 * segMin n m + 1) ^ ones (traceWord n m) :=
  min_term_inequality n m (segMin n m) hend fun _ hi => segMin_le hi

/-! ### Real form -/

/-- **Real form of the min-term bound.**  If the segment strictly climbs and is subcritical
(`3^a < 2^m`), then any positive lower bound `x` of the odd-step values satisfies
`x < a / (3·Λ)`, `Λ = m·log 2 − a·log 3 > 0`.  Uses only `log(1+t) ≤ t`. -/
theorem lowerBound_lt_of_subcritical (n m x : ℕ) (hend : n < tstep^[m] n) (hx1 : 1 ≤ x)
    (hx : ∀ i ∈ oddSteps n m, x ≤ tstep^[i] n) (hsub : 3 ^ ones (traceWord n m) < 2 ^ m) :
    (x : ℝ) < (ones (traceWord n m) : ℝ) /
      (3 * ((m : ℝ) * Real.log 2 - (ones (traceWord n m) : ℝ) * Real.log 3)) := by
  have hnat := min_term_inequality n m x hend hx
  set a := ones (traceWord n m) with ha
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  -- `Λ > 0`
  have hΛ : 0 < (m : ℝ) * Real.log 2 - (a : ℝ) * Real.log 3 := by
    have h := Real.log_lt_log (by positivity) (show ((3 : ℕ) ^ a : ℝ) < (2 : ℕ) ^ m by
      exact_mod_cast hsub)
    push_cast at h
    rw [Real.log_pow, Real.log_pow] at h
    linarith
  -- the real inequality and its logarithm
  have hR : (2 : ℝ) ^ m * (3 * (x : ℝ)) ^ a < 3 ^ a * (3 * (x : ℝ) + 1) ^ a := by
    exact_mod_cast hnat
  have hlog := Real.log_lt_log (by positivity) hR
  have e1 : Real.log ((2 : ℝ) ^ m * (3 * (x : ℝ)) ^ a) =
      (m : ℝ) * Real.log 2 + (a : ℝ) * Real.log (3 * x) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have e2 : Real.log ((3 : ℝ) ^ a * (3 * (x : ℝ) + 1) ^ a) =
      (a : ℝ) * Real.log 3 + (a : ℝ) * Real.log (3 * x + 1) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  rw [e1, e2] at hlog
  -- `log(3x+1) − log(3x) ≤ 1/(3x)`
  have hratio : Real.log (3 * (x : ℝ) + 1) - Real.log (3 * x) ≤ 1 / (3 * x) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < (3 * (x : ℝ) + 1) / (3 * x) by positivity)
    have h3 : (3 * (x : ℝ) + 1) / (3 * x) - 1 = 1 / (3 * x) := by
      field_simp
      ring
    linarith
  have haR : (0 : ℝ) ≤ a := by positivity
  have hkey : (m : ℝ) * Real.log 2 - (a : ℝ) * Real.log 3 < (a : ℝ) * (1 / (3 * x)) := by
    nlinarith [mul_le_mul_of_nonneg_left hratio haR]
  rw [lt_div_iff₀ (by positivity)]
  have h3x : (0 : ℝ) < 3 * x := by positivity
  have := (lt_div_iff₀ h3x).mp (by rw [mul_one_div] at hkey; exact hkey)
  linarith

/-- **Every strictly climbing subcritical segment dips below `a/(3Λ)`.**  In particular every
acyclic paradoxical segment does (`acyclicParadoxical_segMin_lt`). -/
theorem segMin_lt_of_subcritical (n m : ℕ) (hend : n < tstep^[m] n)
    (hsub : 3 ^ ones (traceWord n m) < 2 ^ m) :
    (segMin n m : ℝ) < (ones (traceWord n m) : ℝ) /
      (3 * ((m : ℝ) * Real.log 2 - (ones (traceWord n m) : ℝ) * Real.log 3)) :=
  lowerBound_lt_of_subcritical n m (segMin n m) hend
    (one_le_segMin (oddSteps_nonempty_of_lt n m hend)) (fun _ hi => segMin_le hi) hsub

theorem acyclicParadoxical_segMin_lt (n m : ℕ) (h : AcyclicParadoxical n m) :
    (segMin n m : ℝ) < (ones (traceWord n m) : ℝ) /
      (3 * ((m : ℝ) * Real.log 2 - (ones (traceWord n m) : ℝ) * Real.log 3)) :=
  segMin_lt_of_subcritical n m h.2.2.2 h.2.2.1

/-! ### Corollary with the Rhin-lite separation

**Trust ledger.**  Everything above is standard trust triple.  The declarations below inherit
the eleven explicitly allow-listed Rhin-lite `native_decide` certificates through
`rhinLite_log23_measure` (the same inheritance as the fixed-run length theorem
`acyclicParadoxical_length_lt_of_oddRunCount`). -/

/-- Off the near-critical window, `Λ ≥ log 2`. -/
theorem log23_ge_log_two_of_off_window (k m : ℕ) (h : 2 * 3 ^ k ≤ 2 ^ m) :
    Real.log 2 ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
  have hR : (2 : ℝ) * 3 ^ k ≤ 2 ^ m := by exact_mod_cast h
  have := Real.log_le_log (by positivity) hR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at this
  linarith

/-- **Polynomial trunk bound.**  Every acyclic paradoxical segment has an odd-step value
`x_min < a^437 / (3·rhinLiteSepC) + a`, where `a` is its odd-step count.
Inherits the Rhin-lite native certificates (see the section docstring). -/
theorem segMin_lt_poly_of_acyclicParadoxical (n m : ℕ) (h : AcyclicParadoxical n m) :
    (segMin n m : ℝ) <
      (ones (traceWord n m) : ℝ) ^ 437 / (3 * rhinLiteSepC) + ones (traceWord n m) := by
  have hlt := acyclicParadoxical_segMin_lt n m h
  set a := ones (traceWord n m) with ha
  have ha1 : 1 ≤ a := one_le_ones_of_lt n m h.2.2.2
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hc := rhinLiteSepC_pos
  set Λ : ℝ := (m : ℝ) * Real.log 2 - (a : ℝ) * Real.log 3 with hΛ
  have hapos : (0 : ℝ) < a := by linarith
  have hpoly : (0 : ℝ) ≤ (a : ℝ) ^ 437 / (3 * rhinLiteSepC) := by positivity
  rcases lt_or_ge (2 ^ m) (2 * 3 ^ a) with hwin | hoff
  · -- near-critical window: `Λ ≥ c / a^436`
    have hmeas := rhinLite_log23_measure a m ha1 h.2.2.1 hwin
    rw [← hΛ] at hmeas
    have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hmeas
    have hle : (a : ℝ) / (3 * Λ) ≤ (a : ℝ) ^ 437 / (3 * rhinLiteSepC) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : rhinLiteSepC ≤ Λ * (a : ℝ) ^ 436 := by
        have := (div_le_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) ^ 436)).mp hmeas
        linarith
      have h2 : (a : ℝ) ^ 437 = (a : ℝ) ^ 436 * a := by ring
      rw [h2]
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 3 * a)]
    linarith
  · -- off the window: `Λ ≥ log 2 > 1/3`, so `a/(3Λ) < a`
    have hl2 := log23_ge_log_two_of_off_window a m hoff
    rw [← hΛ] at hl2
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hΛpos : 0 < Λ := by linarith
    have hle : (a : ℝ) / (3 * Λ) < a := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

set_option exponentiation.threshold 6001 in
/-- The same bound in pure `ℕ` with the constant unfolded:
`x_min < 396^6000 · 6^436 · a^437`. -/
theorem segMin_lt_nat_poly_of_acyclicParadoxical (n m : ℕ) (h : AcyclicParadoxical n m) :
    segMin n m < 396 ^ 6000 * 6 ^ 436 * ones (traceWord n m) ^ 437 := by
  have hlt := segMin_lt_poly_of_acyclicParadoxical n m h
  set a := ones (traceWord n m) with ha
  have ha1 : 1 ≤ a := one_le_ones_of_lt n m h.2.2.2
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hK : (2 : ℝ) ≤ (396 : ℝ) ^ 6000 * 6 ^ 436 := by
    have h1 : (396 : ℝ) ≤ 396 ^ 6000 := le_self_pow₀ (by norm_num) (by norm_num)
    have h2 : (1 : ℝ) ≤ 6 ^ 436 := one_le_pow₀ (by norm_num)
    calc (2 : ℝ) ≤ 396 * 1 := by norm_num
      _ ≤ 396 ^ 6000 * 6 ^ 436 := mul_le_mul h1 h2 (by norm_num) (by positivity)
  have h5 : (5 : ℝ) ≤ 5 ^ 6000 := le_self_pow₀ (by norm_num) (by norm_num)
  have hpow : (a : ℝ) ≤ (a : ℝ) ^ 437 := le_self_pow₀ haR (by norm_num)
  set K : ℝ := (396 : ℝ) ^ 6000 * 6 ^ 436 with hKdef
  clear_value K
  have hcval : (a : ℝ) ^ 437 / (3 * rhinLiteSepC) = 2 * (K / 5 ^ 6000) * (a : ℝ) ^ 437 / 3 := by
    unfold rhinLiteSepC
    rw [hKdef, div_pow, mul_div_assoc]
    field_simp
  rw [hcval] at hlt
  have hbound : 2 * (K / 5 ^ 6000) * (a : ℝ) ^ 437 / 3 + a ≤ K * (a : ℝ) ^ 437 := by
    have hKa : (0 : ℝ) ≤ K * (a : ℝ) ^ 437 := by positivity
    have hdiv : K / 5 ^ 6000 ≤ K / 5 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) h5
    have hapow : (0 : ℝ) ≤ (a : ℝ) ^ 437 := by positivity
    have h1 : 2 * (K / 5 ^ 6000) * (a : ℝ) ^ 437 / 3 ≤ 2 * (K / 5) * (a : ℝ) ^ 437 / 3 := by
      gcongr
    have h2 : (a : ℝ) ≤ K * (a : ℝ) ^ 437 / 2 := by
      have : 2 * (a : ℝ) ^ 437 ≤ K * (a : ℝ) ^ 437 := mul_le_mul_of_nonneg_right hK hapow
      linarith
    have h3 : 2 * (K / 5) * (a : ℝ) ^ 437 / 3 = (2 / 15) * (K * (a : ℝ) ^ 437) := by ring
    linarith
  have hR : (segMin n m : ℝ) < K * (a : ℝ) ^ 437 := lt_of_lt_of_le hlt hbound
  have hcast : ((396 ^ 6000 * 6 ^ 436 * a ^ 437 : ℕ) : ℝ) = K * (a : ℝ) ^ 437 := by
    rw [hKdef, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow]
    norm_cast
  rw [← hcast] at hR
  exact_mod_cast hR

/-! ### Kernel control on `(7, 8)` -/

/-- **Kernel control.**  On `AcyclicParadoxical 7 8` (`7 → 11 → 17 → 26 → 13 → 20 → 10 → 5 → 8`):
odd steps at indices `0,1,2,4,7` with values `7, 11, 17, 13, 5`, so `x_min = 5`, `a = 5`, and the
min-term inequality reads `2^8 · 15^5 = 194400000 < 254803968 = 3^5 · 16^5`. -/
theorem trunkBound_control_seven_eight :
    oddSteps 7 8 = {0, 1, 2, 4, 7} ∧
    (oddSteps 7 8).image (fun i => tstep^[i] 7) = {7, 11, 17, 13, 5} ∧
    segMin 7 8 = 5 ∧ ones (traceWord 7 8) = 5 ∧
    2 ^ 8 * (3 * 5) ^ 5 = 194400000 ∧ 3 ^ 5 * (3 * 5 + 1) ^ 5 = 254803968 ∧
    2 ^ 8 * (3 * 5) ^ 5 < 3 ^ 5 * (3 * 5 + 1) ^ 5 := by
  decide +kernel

/-- The product identity, instantiated on the control segment: both sides are
`2^8 · 8 · (21·33·51·39·15) = 3^5 · 7 · (22·34·52·40·16)`. -/
theorem prod_identity_control_seven_eight :
    2 ^ 8 * tstep^[8] 7 * ∏ i ∈ oddSteps 7 8, (3 * tstep^[i] 7) =
      3 ^ ones (traceWord 7 8) * 7 * ∏ i ∈ oddSteps 7 8, (3 * tstep^[i] 7 + 1) ∧
    2 ^ 8 * tstep^[8] 7 * ∏ i ∈ oddSteps 7 8, (3 * tstep^[i] 7) = 2 ^ 8 * 8 * (21 * 33 * 51 * 39 * 15) := by
  decide +kernel

end CollatzMoonshot.FrontA
