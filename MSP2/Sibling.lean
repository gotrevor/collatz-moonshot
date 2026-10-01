/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MSP2.Defs

/-!
# MSP²: the `3x − 1` sibling, where `Raccord` fails

The authors' 2026-10-01 note *Structural Recurrence of the Generator Table* (Route A, §§9-13)
argues for the open step by a finiteness-versus-growth mechanism: the `3ʳk + B` side has a
finite vertical loop of period `2·3ʳ⁻¹`, the companion `2ᵐk + Cₘ` keeps doubling, so a
connection must occur after finitely many rows.

That vertical loop is `tA`, multiplication by `2⁻¹` modulo `3ʳ` (`MSP2.Order`), and its period
is `orderOf_two_zmod` - neither depends on the `+1` in `3x + 1`.  The companion doubling and the
row / wall combinatorics depend only on parity branching.  So the mechanism's ingredients hold
equally for the `3x − 1` map, and there the conclusion is false: `5 → 14 → 7 → 20 → 10 → 5`
never dips below `5`.  A sound mechanism for `Raccord` must therefore use something that
separates `+1` from `−1`.
-/

namespace MSP2

/-- The `3x − 1` sibling of `CollatzMoonshot.step`. -/
def stepMinus (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n - 1

/-- `Covered` for the `3x − 1` sibling. -/
def CoveredMinus (N : ℕ) : Prop := ∃ j, stepMinus^[j] N < N

/-- `Raccord` transcribed to the `3x − 1` sibling. -/
def RaccordMinus : Prop := ∀ n, ∀ N, 2 ≤ N → N ≤ 2 ^ n - 1 → CoveredMinus N

/-- The orbit of `5` under `3x − 1` is the cycle `5, 14, 7, 20, 10`. -/
theorem stepMinus_iterate_five (j : ℕ) :
    stepMinus^[j] 5 ∈ ({5, 14, 7, 20, 10} : Finset ℕ) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    generalize stepMinus^[j] 5 = x at ih ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at ih
    rcases ih with rfl | rfl | rfl | rfl | rfl <;> decide

/-- `5` is never covered under `3x − 1`. -/
theorem not_coveredMinus_five : ¬ CoveredMinus 5 := by
  rintro ⟨j, hj⟩
  have h := stepMinus_iterate_five j
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  omega

/-- **`Raccord` is false for the `3x − 1` sibling**, already at level `3`. -/
theorem not_raccordMinus : ¬ RaccordMinus :=
  fun h => not_coveredMinus_five (h 3 5 (by norm_num) (by norm_num))

end MSP2
