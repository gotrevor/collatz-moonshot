/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Basic definitions: the Collatz map and its orbits

The un-accelerated Collatz map on `ℕ` (halve if even, `3n + 1` if odd), plus the
handful of orbit facts everything else leans on: positivity is preserved, and the
forward orbit of `1` is the trivial cycle `1 → 4 → 2 → 1`.
-/

namespace CollatzMoonshot

/-- The Collatz map: halve if even, `3n + 1` if odd. -/
def step (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

@[simp] theorem step_one : step 1 = 4 := by decide

@[simp] theorem step_two : step 2 = 1 := by decide

@[simp] theorem step_four : step 4 = 2 := by decide

/-- The Collatz map preserves positivity. -/
theorem step_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ step n := by
  unfold step
  split <;> omega

/-- Every point of a positive orbit is positive. -/
theorem iterate_step_pos {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : 1 ≤ step^[k] n := by
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact step_pos ih

/-- The forward orbit of `1` is the trivial cycle `1 → 4 → 2 → 1`. -/
theorem iterate_one_mem (k : ℕ) : step^[k] 1 = 1 ∨ step^[k] 1 = 4 ∨ step^[k] 1 = 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h | h <;> rw [h] <;> decide

/-- `n` eventually reaches `1` under iteration of `step`. -/
def ReachesOne (n : ℕ) : Prop := ∃ k, step^[k] n = 1

theorem reachesOne_one : ReachesOne 1 := ⟨0, by decide⟩

theorem reachesOne_two : ReachesOne 2 := ⟨1, by decide⟩

theorem reachesOne_four : ReachesOne 4 := ⟨2, by decide⟩

end CollatzMoonshot
