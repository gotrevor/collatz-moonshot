/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalCycleBound

/-!
# No amusical itinerary is base-3 normal (research §54)

Label each step of a `U`-orbit by its branch (`stepSym`: 0 even, 1 for `4n + 1`, 2 for `4n + 3`).
The "normal" agent (2026-10-15) asked whether the itinerary of an infinite orbit, read as a base-3
real, can be normal.  It cannot: normality would give the even label frequency `1/3`.

* An aperiodic orbit cannot have even-frequency `1/3 < log₂(4/3)`: such an orbit spends more than
  `log₂ 3` bits per step and falls (`periodic_of_evenFrequency_lt`, `AmusicalEscape.lean`).
* A cycle cannot have even-frequency `1/3` either.  Around a cycle of length `p` with `E` even
  steps the product of the step ratios is 1, so `3^p · ∏_{odd x} (1 + ε(x)/(3x)) = 2^{2p − E}`.
  At `E = p/3` the odd factors must average at least `(2^{5/3}/3)^{3/2} ≈ 1.089`, forcing odd cycle
  elements `≤ 3`; the only such cycles are `{1}` (frequency 0) and `{2, 3}` (frequency `1/2`).

* `not_tendsto_evenFrequency_third`: for every positive integer, the even-label frequency of its
  forward itinerary does not tend to `1/3`.  So no positive integer's itinerary is base-3 normal.

Route in Lean: along the times `q p` the frequency is the constant `E / p`, so `3E = p`
(`three_mul_evenStepCount_of_tendsto`).  If every cycle element is `≥ 4`, Theorem A★
(`amusical_cycle_min_bound`, lower bound `4`) gives `2^{5E} 12^{2E} ≤ 3^{3E} 13^{2E}`, i.e.
`4608^E ≤ 4563^E`, false.  Otherwise some element lies in `[0, 4)`, which is backward
invariant, so `m ∈ {1, 2, 3}`, and periods `1`, `2`, `2` give `3E ≠ p` by `decide`.
-/

namespace CollatzMoonshot.Amusical

/-- The number of even steps among the first `k` forward steps from `m`. -/
def evenStepCount (m : ℤ) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun j => stepSym (amusical^[j] m) = 0).card

theorem evenStepCount_eq_count (m : ℤ) (k : ℕ) :
    evenStepCount m k = Nat.count (fun j => stepSym (amusical^[j] m) = 0) k :=
  (Nat.count_eq_card_filter_range _ _).symm

/-- **Proved.**  Over `q` full periods the even count is `q` times the count over one period. -/
theorem evenStepCount_mul_period {m : ℤ} {p : ℕ} (hcyc : amusical^[p] m = m) (q : ℕ) :
    evenStepCount m (q * p) = q * evenStepCount m p := by
  induction q with
  | zero => simp [evenStepCount]
  | succ q ih =>
      have hq : amusical^[q * p] m = m :=
        Function.IsPeriodicPt.const_mul (f := amusical) hcyc q
      have hper : ∀ i, amusical^[q * p + i] m = amusical^[i] m := by
        intro i
        rw [add_comm, Function.iterate_add_apply, hq]
      rw [evenStepCount_eq_count, add_mul, one_mul, Nat.count_add, ← evenStepCount_eq_count, ih]
      simp_rw [hper]
      rw [← evenStepCount_eq_count, add_mul, one_mul]

/-- **Proved.**  The even steps plus the bits spent equal two per step. -/
theorem sum_stepBits_add_evenStepCount (m : ℤ) (k : ℕ) :
    (∑ j ∈ Finset.range k, stepBits (amusical^[j] m)) + evenStepCount m k = 2 * k := by
  induction k with
  | zero => simp [evenStepCount]
  | succ k ih =>
      rw [evenStepCount_eq_count] at ih ⊢
      rw [Finset.sum_range_succ, Nat.count_succ]
      have hs : stepBits (amusical^[k] m) +
          (if stepSym (amusical^[k] m) = 0 then 1 else 0) = 2 := by
        unfold stepBits stepSym
        split_ifs <;> simp_all
      split_ifs at hs ⊢ <;> omega

/-- **Proved.**  If `m` has period `p ≥ 1` and its even frequency tends to `1/3`, then exactly a
third of the steps in one period are even: the frequency at times `q p` is constantly `E / p`. -/
theorem three_mul_evenStepCount_of_tendsto {m : ℤ} {p : ℕ} (hp : 1 ≤ p) (hcyc : amusical^[p] m = m)
    (h : Filter.Tendsto (fun k : ℕ => (evenStepCount m k : ℝ) / k) Filter.atTop (nhds (1 / 3))) :
    3 * evenStepCount m p = p := by
  have hmul : Filter.Tendsto (fun q : ℕ => q * p) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 fun b =>
      ⟨b, fun q hq => le_trans hq (Nat.le_mul_of_pos_right _ hp)⟩
  have hsub := h.comp hmul
  have hconst : Filter.Tendsto (fun _ : ℕ => (evenStepCount m p : ℝ) / p) Filter.atTop
      (nhds (1 / 3)) := by
    apply hsub.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with q hq
    simp only [Function.comp, evenStepCount_mul_period hcyc q]
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    push_cast
    rw [mul_div_mul_left _ _ hq0]
  have heq := tendsto_nhds_unique tendsto_const_nhds hconst
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  field_simp at heq
  have h2 : p = evenStepCount m p * 3 := by exact_mod_cast heq.symm
  omega

/-- **Proved (research §54).**  No positive integer's forward `U`-itinerary has even-label
frequency tending to `1/3`; in particular, read in base 3, no such itinerary is normal. -/
theorem not_tendsto_evenFrequency_third (m : ℤ) (hm : 0 < m) :
    ¬ Filter.Tendsto (fun k : ℕ =>
      (((Finset.range k).filter fun j => stepSym (amusical^[j] m) = 0).card : ℝ) / k)
      Filter.atTop (nhds (1 / 3)) := by
  intro h
  have h' : Filter.Tendsto (fun k : ℕ => (evenStepCount m k : ℝ) / k) Filter.atTop
      (nhds (1 / 3)) := h
  have hc : (1 / 3 : ℝ) < 2 - Real.logb 2 3 := by
    have hlog : Real.logb 2 3 < (5 : ℝ) / 3 :=
      (CollatzMoonshot.FrontA.logb_two_three_lt_iff 5 3 (by norm_num)).2 (by norm_num)
    linarith
  obtain ⟨p, hp, hcyc⟩ := periodic_of_evenFrequency_lt m (1 / 3) hc h
  have h3 := three_mul_evenStepCount_of_tendsto hp hcyc h'
  by_cases h4 : ∀ j < p, 4 ≤ amusical^[j] m
  · have hb := (amusical_cycle_min_bound m 4 p (by omega) hcyc (by norm_num) h4).2
    have hsum := sum_stepBits_add_evenStepCount m p
    set E := evenStepCount m p
    set e := ∑ j ∈ Finset.range p, stepBits (amusical^[j] m)
    have he : e = 5 * E := by omega
    have hk : e - p = 2 * E := by omega
    have hp3 : p = 3 * E := by omega
    have hE : E ≠ 0 := by omega
    rw [hk, he, hp3, pow_mul, pow_mul, pow_mul, pow_mul, ← mul_pow, ← mul_pow] at hb
    norm_num at hb
    exact absurd hb (not_le.2 (pow_lt_pow_left₀ (by norm_num) (by norm_num) hE))
  · push Not at h4
    obtain ⟨j, -, hj⟩ := h4
    have hnn : ∀ i : ℕ, 0 ≤ amusical^[i] m := by
      intro i
      induction i with
      | zero => exact hm.le
      | succ i ih => rw [Function.iterate_succ_apply']; exact amusical_nonneg ih
    obtain ⟨-, hm4⟩ := nonneg_of_iterate_lt_four j m (hnn j) hj
    have key : ∀ q : ℕ, 1 ≤ q → amusical^[q] m = m → 3 * evenStepCount m q = q :=
      fun q hq hqc => three_mul_evenStepCount_of_tendsto hq hqc h'
    have hm3 : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hm3 with rfl | rfl | rfl
    · have := key 1 le_rfl (by decide)
      revert this; decide
    · have := key 2 (by norm_num) (by decide)
      revert this; decide
    · have := key 2 (by norm_num) (by decide)
      revert this; decide

end CollatzMoonshot.Amusical
