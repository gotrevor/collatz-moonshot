/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.Rigidity.Drift

/-!
# Front B as a Diophantine squeeze on `log 2` and `log 3`

Assume a nontrivial cycle exists.  Write `a` for its odd steps and `b` for its
even steps.  Because the orbit returns to its starting value exactly, the drift
bookkeeping of `Rigidity/Drift.lean` closes into a **two-sided** statement:

* dropping the `+1` undercounts, so `3^a ≤ 2^b` (and `3^a ≠ 2^b` by parity, so the
  inequality is strict);
* throttling the `+1` by the cycle's minimum element `N` overcounts, so
  `2^b ≤ (3 + 1/N)^a`.

Together: `3^a < 2^b ≤ (3 + 1/N)^a`.  In logarithms,

`0 < b·log 2 − a·log 3 ≤ a·log(1 + 1/(3N)) ≤ a/(3N)`.

So a cycle whose elements all exceed `N` forces `b/a` to approximate `log₂ 3` to
within about `1/(3N)` per odd step.  **The cycle hypothesis manufactures an
extraordinarily good rational approximation to `log₂ 3`** - which is exactly why
every unconditional cycle result in the literature is a Diophantine result.

## What this does and does not buy

It buys **lower bounds on cycle length**: pair the squeeze with a computed
continued-fraction expansion of `log₂ 3` (or with an effective irrationality
measure) and every short `a` is excluded, because `log₂ 3` has no good
approximation with small denominator.  This is the mechanism behind the Eliahou
bound axiomatised in `Assumed/Cycles.lean` - i.e. **this file is the honest road
to *deriving* that axiom rather than citing it.**

It does **not** buy a contradiction, and the reason is structural: `log₂ 3` is
irrational, so arbitrarily good approximations `b/a` exist.  No fixed
impossibility lives in the pair `(log 2, log 3)` alone.  The squeeze converts
"verified up to `N`" into "no cycle shorter than roughly `√N`", and that is all
it can ever do by itself.  A contradiction has to come from the *exponent
structure* - which halving-run lengths are dynamically realisable - not from the
two logarithms.
-/

namespace CollatzMoonshot

/-- `3^a` and `2^b` are never equal once `a ≥ 1`: one is odd and exceeds `1`. -/
theorem three_pow_ne_two_pow {a b : ℕ} (ha : 1 ≤ a) : (3:ℕ) ^ a ≠ 2 ^ b := by
  intro h
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    simp only [pow_zero, Nat.pow_eq_one] at h
    omega
  · have h2 : (2:ℕ) ∣ 3 ^ a := by rw [h]; exact dvd_pow_self 2 (by omega)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    omega

/-- **Lower half of the squeeze**: a cycle forces `3^a ≤ 2^b`. -/
theorem three_pow_le_two_pow_of_cycle {n p : ℕ} (hn : 1 ≤ n) (hcyc : step^[p] n = n) :
    3 ^ oddSteps n p ≤ 2 ^ evenSteps n p := by
  have h := mul_three_pow_le n p
  rw [hcyc] at h
  exact Nat.le_of_mul_le_mul_left h hn

/-- **Upper half of the squeeze**: a cycle whose elements never drop below `N`
forces `2^b ≤ (3 + 1/N)^a`. -/
theorem two_pow_le_growth_pow_of_cycle {n N p : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hcyc : step^[p] n = n) (hfloor : ∀ j < p, N ≤ step^[j] n) :
    (2:ℝ) ^ evenSteps n p ≤ growth N ^ oddSteps n p := by
  have h := iterate_mul_two_pow_le hN p hfloor
  rw [hcyc] at h
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  exact le_of_mul_le_mul_left h hn0

/-- A positive cycle of positive period takes at least one odd step: an
all-halving cycle would have to satisfy `2^b ≤ 1`. -/
theorem one_le_oddSteps_of_cycle {n p : ℕ} (hn : 1 ≤ n) (hp : 0 < p)
    (hcyc : step^[p] n = n) : 1 ≤ oddSteps n p := by
  by_contra hzero
  have ha : oddSteps n p = 0 := by omega
  have hfloor : ∀ j < p, 1 ≤ step^[j] n := fun j _ => iterate_step_pos hn j
  have h := two_pow_le_growth_pow_of_cycle hn le_rfl hcyc hfloor
  rw [ha, pow_zero] at h
  have hb : evenSteps n p = 0 := by
    by_contra hb
    have h1 : (2:ℝ) ≤ 2 ^ evenSteps n p := by
      calc (2:ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ evenSteps n p := by
            exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have := oddSteps_add_evenSteps n p
  omega

/-- **The squeeze**, integer form: a nontrivial cycle pins `2^b` strictly between
`3^a` and `(3 + 1/N)^a`, where `N` is any floor its elements respect. -/
theorem cycle_squeeze {n N p : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (hp : 0 < p)
    (hcyc : step^[p] n = n) (hfloor : ∀ j < p, N ≤ step^[j] n) :
    (3:ℝ) ^ oddSteps n p < 2 ^ evenSteps n p ∧
      (2:ℝ) ^ evenSteps n p ≤ growth N ^ oddSteps n p := by
  refine ⟨?_, two_pow_le_growth_pow_of_cycle hn hN hcyc hfloor⟩
  have hle := three_pow_le_two_pow_of_cycle hn hcyc
  have hne := three_pow_ne_two_pow (b := evenSteps n p) (one_le_oddSteps_of_cycle hn hp hcyc)
  have : (3:ℕ) ^ oddSteps n p < 2 ^ evenSteps n p := lt_of_le_of_ne hle hne
  exact_mod_cast this

/-- **The squeeze in logarithms** - the form the Diophantine literature uses.
A nontrivial cycle whose elements all exceed `N` makes the linear form
`b·log 2 − a·log 3` positive but smaller than `a/(3N)`: the cycle *manufactures*
a rational approximation `b/a` to `log₂ 3` of quality `1/(3N)` per odd step.

This is the precise statement behind "a cycle would force an impossible
relationship between `log 2` and `log 3`".  It is not impossible - it is only
*expensive*, and how expensive is what bounds cycle length. -/
theorem log_linear_form_bounds {n N p : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (hp : 0 < p)
    (hcyc : step^[p] n = n) (hfloor : ∀ j < p, N ≤ step^[j] n) :
    0 < evenSteps n p * Real.log 2 - oddSteps n p * Real.log 3 ∧
      evenSteps n p * Real.log 2 - oddSteps n p * Real.log 3
        ≤ oddSteps n p / (3 * N) := by
  obtain ⟨hlow, hhigh⟩ := cycle_squeeze hn hN hp hcyc hfloor
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  constructor
  · have := Real.log_lt_log (by positivity) hlow
    rw [Real.log_pow, Real.log_pow] at this
    linarith
  · -- `3 + 1/N = 3 * (1 + 1/(3N))`, and `log (1 + x) ≤ x`
    have hfac : growth N = 3 * (1 + 1 / (3 * (N:ℝ))) := by unfold growth; field_simp
    have hsplit : Real.log (growth N) = Real.log 3 + Real.log (1 + 1 / (3 * (N:ℝ))) := by
      rw [hfac, Real.log_mul (by norm_num) (by positivity)]
    have hsmall : Real.log (1 + 1 / (3 * (N:ℝ))) ≤ 1 / (3 * (N:ℝ)) := by
      have := Real.log_le_sub_one_of_pos (x := 1 + 1 / (3 * (N:ℝ))) (by positivity)
      linarith
    have hlog := Real.log_le_log (by positivity) hhigh
    rw [Real.log_pow, Real.log_pow, hsplit, mul_add] at hlog
    have hodd0 : (0:ℝ) ≤ (oddSteps n p : ℝ) := by positivity
    have hmul : (oddSteps n p : ℝ) * Real.log (1 + 1 / (3 * (N:ℝ)))
        ≤ (oddSteps n p : ℝ) * (1 / (3 * (N:ℝ))) := mul_le_mul_of_nonneg_left hsmall hodd0
    have hgoal : (oddSteps n p : ℝ) / (3 * N) = (oddSteps n p : ℝ) * (1 / (3 * (N:ℝ))) := by
      ring
    rw [hgoal]
    linarith

/-! ## Sharpness check

The trivial cycle `1 → 4 → 2 → 1` has `a = 1` odd step, `b = 2` even steps and
minimum element `1`, so the squeeze reads `3 < 4 ≤ (3 + 1/1)^1 = 4`: the upper
half is **attained exactly**.  The estimate is sharp and the statement is not
vacuous - a cycle sitting at the floor `N = 1` has no room at all, and every unit
of room comes from the elements being large. -/

example : oddSteps 1 3 = 1 ∧ evenSteps 1 3 = 2 := by
  constructor <;> rfl

example : step^[3] 1 = 1 := by rfl

end CollatzMoonshot
