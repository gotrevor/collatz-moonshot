/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.FirstCrossing

/-!
# The coefficient stopping-time conjecture kills Front B

`FirstCrossing.StoppingCorrect` - "at the first coefficient crossing the accelerated
orbit is already below its start" - is stated for *every* start `n ≥ 2`, with no
finiteness hypothesis.  That is enough, by itself, to settle the cycle front: no
`CrossingExists` input is needed, because a cycle *manufactures* its own crossing.

The argument:

* a `step`-cycle gives an accelerated (`tstep`) cycle through some `n' ≥ 1`
  (`FrontB.tstep_cycle_of_step_cycle`);
* the accelerated orbit of `n'` is a finite set of positive integers, so it has a
  minimum `n₀`, which is itself `tstep`-periodic with the same period `p`;
* over one full period the iterate identity reads
  `2^p · n₀ = 3^(ones w) · n₀ + numer w` with `numer w > 0`, so `3^(ones w) < 2^p`:
  **the full period is subcritical**, i.e. `n₀` has a coefficient crossing;
* `exists_first_crossing` extracts the *first* one, and `StoppingCorrect` (usable
  as soon as `n₀ ≥ 2`) drops the orbit strictly below `n₀` - impossible for the
  orbit minimum.  Hence `n₀ = 1`, the cycle is the trivial accelerated `{1,2}`
  two-cycle, and the original `step`-member lies in `{1, 2, 4}`.

So `StoppingCorrect → NoNontrivialCycle`: the coefficient stopping-time conjecture
is *not* a Front A-only statement; it already contains all of Front B.  Equivalently,
Front B is a lower bound on the difficulty of `StoppingCorrect`, which is the honest
reason `conjecture_of_stoppingCorrect_and_crossingExists` is not a cheap route.
-/

namespace CollatzMoonshot.FrontA.FirstCrossing

open CollatzMoonshot CollatzMoonshot.FrontB

/-- The accelerated orbit of `1` is the two-cycle `{1, 2}`. -/
theorem tstep_iterate_one (p : ℕ) : tstep^[p] 1 = 1 ∨ tstep^[p] 1 = 2 := by
  induction p with
  | zero => exact Or.inl rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h <;> rw [h] <;> simp

/-- A full period of an accelerated cycle is subcritical: the cycle's own parity word
has strictly more halvings than the `3^k` it accumulates.  Immediate from the iterate
identity and positivity of the numerator. -/
theorem full_period_subcritical {n p : ℕ} (hn : 1 ≤ n) (hp : 0 < p)
    (hcyc : tstep^[p] n = n) : 3 ^ ones (traceWord n p) < 2 ^ p := by
  have hid := tstep_iterate_identity p n
  rw [hcyc] at hid
  have hnum : 0 < numer (traceWord n p) := numer_pos (ones_pos_of_cycle hn hp hcyc)
  have h3 : 3 ^ ones (traceWord n p) * n < 2 ^ p * n := by omega
  exact lt_of_mul_lt_mul_right h3 (Nat.zero_le n)

/-- **The helper.**  Under `StoppingCorrect`, every accelerated cycle member is `1`
or `2`.  The orbit minimum `n₀` cannot be `≥ 2`: its own period is a crossing, the
first crossing descends strictly below `n₀`, and the descended value is again on the
orbit. -/
theorem tstep_cycle_member_trivial_of_stoppingCorrect (h : StoppingCorrect)
    {n p : ℕ} (hn : 1 ≤ n) (hp : 0 < p) (hcyc : tstep^[p] n = n) :
    n = 1 ∨ n = 2 := by
  classical
  -- the orbit minimum
  have hex : ∃ x, ∃ i, tstep^[i] n = x := ⟨n, 0, rfl⟩
  obtain ⟨i₀, hi₀⟩ := Nat.find_spec hex
  set n₀ := Nat.find hex with hn₀def
  have hmin : ∀ i, n₀ ≤ tstep^[i] n := fun i => Nat.find_le ⟨i, rfl⟩
  have hn₀pos : 1 ≤ n₀ := hi₀ ▸ tstep_iterate_pos hn i₀
  -- periodicity of the minimum
  have hshift : ∀ j, tstep^[j] n₀ = tstep^[j + i₀] n := by
    intro j
    rw [Function.iterate_add_apply, hi₀]
  have hcyc₀ : tstep^[p] n₀ = n₀ := by
    rw [hshift p, show p + i₀ = i₀ + p by omega, Function.iterate_add_apply, hcyc, hi₀]
  have hmin₀ : ∀ j, n₀ ≤ tstep^[j] n₀ := by
    intro j; rw [hshift j]; exact hmin _
  -- the minimum is `1`
  have hn₀one : n₀ = 1 := by
    by_contra hne
    have h2 : 2 ≤ n₀ := by omega
    obtain ⟨m, hm⟩ := exists_first_crossing
      ⟨p, full_period_subcritical hn₀pos hp hcyc₀⟩
    exact absurd (hmin₀ m) (not_le.mpr (h n₀ m h2 hm))
  -- the whole cycle is the accelerated two-cycle `{1, 2}`
  have hback : tstep^[p * (i₀ + 1) - i₀] n₀ = n := by
    rw [hshift, show p * (i₀ + 1) - i₀ + i₀ = p * (i₀ + 1) by
      have : i₀ + 1 ≤ p * (i₀ + 1) := Nat.le_mul_of_pos_left _ hp
      omega]
    rw [Function.iterate_mul]
    exact Function.iterate_fixed hcyc _
  rw [hn₀one] at hback
  rcases tstep_iterate_one (p * (i₀ + 1) - i₀) with hx | hx
  · exact Or.inl (hback ▸ hx)
  · exact Or.inr (hback ▸ hx)

/-- **The implication.**  The coefficient stopping-time conjecture implies Front B:
no nontrivial Collatz cycle. -/
theorem noNontrivialCycle_of_stoppingCorrect
    (h : StoppingCorrect) : CollatzMoonshot.NoNontrivialCycle := by
  intro n hn hc
  obtain ⟨n', p, hn', hp, hcycle, hrel⟩ := tstep_cycle_of_step_cycle hn hc
  exact step_member_trivial
    (tstep_cycle_member_trivial_of_stoppingCorrect h hn' hp hcycle) hrel

end CollatzMoonshot.FrontA.FirstCrossing
