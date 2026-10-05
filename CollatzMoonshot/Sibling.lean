/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Sibling maps `T_{q,c}`: the known-negative controls as theorems

`RESEARCH-2026-09-29-map-controls.md` runs the certificate-repair toolkit on maps where
convergence is known to fail.  This file records its anchors in the kernel, so the
**sibling-transfer** gate of `Maze.lean` cites theorems rather than a sentence.

`T_{q,c}(x) = (q x + c)/2` for odd `x`, `x/2` for even `x`.  The controls are `(3,-1)` and
`(5,1)`.  For 3x−1: the cycle `5 → 7 → 10 → 5` and the scalar certificate
`5 = 2^4 · s₁₁ s₂₅ s₃₇` with `s_u = u / T_{3,-1}(u)`.  So a scalar certificate exists at a start
that never reaches 1.
-/

namespace CollatzMoonshot.Sibling

/-- The generalized Collatz map `T_{q,c}` on `ℤ`. -/
def T (q c : ℤ) (x : ℤ) : ℤ := if x % 2 = 0 then x / 2 else (q * x + c) / 2

/-- The edge ratio `u / T_{q,c}(u)`. -/
def ratio (q c : ℤ) (u : ℤ) : ℚ := (u : ℚ) / (T q c u : ℚ)

/-- 3x−1 has the cycle `5 → 7 → 10 → 5`. -/
theorem threeMinus_cycle_five :
    T 3 (-1) 5 = 7 ∧ T 3 (-1) 7 = 10 ∧ T 3 (-1) 10 = 5 := by decide

/-- Hence 5 never reaches 1 under 3x−1: its orbit is `{5, 7, 10}`. -/
theorem threeMinus_five_orbit (k : ℕ) : (T 3 (-1))^[k] 5 ∈ ({5, 7, 10} : Finset ℤ) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [Finset.mem_insert, Finset.mem_singleton] at ih ⊢
    rcases ih with h | h | h <;> rw [h] <;> decide

theorem threeMinus_five_ne_one (k : ℕ) : (T 3 (-1))^[k] 5 ≠ 1 := by
  intro h
  have := threeMinus_five_orbit k
  rw [h] at this
  exact absurd this (by decide)

/-- The scalar certificate `5 = 2^4 · s₁₁ s₂₅ s₃₇` for 3x−1 (map-controls, first row). -/
theorem threeMinus_certificate_five :
    (2 : ℚ) ^ 4 * ratio 3 (-1) 11 * ratio 3 (-1) 25 * ratio 3 (-1) 37 = 5 := by
  norm_num [ratio, T]

/-- 5x+1 has the cycle `13 → 33 → 83 → 208 → 104 → 52 → 26 → 13`. -/
theorem fivePlus_cycle_thirteen :
    T 5 1 13 = 33 ∧ T 5 1 33 = 83 ∧ T 5 1 83 = 208 ∧ T 5 1 208 = 104 ∧
      T 5 1 104 = 52 ∧ T 5 1 52 = 26 ∧ T 5 1 26 = 13 := by decide

/-- The unit two-count inequality separates 3x−1 (cycle 5: `3^2 > 2^3`) but not 5x+1
(cycle 13: `5^3 < 2^7`, the same direction as the 3x+1 unit U8: `3^5 < 2^8`). -/
theorem unit_two_count_controls :
    (3 : ℕ) ^ 2 > 2 ^ 3 ∧ (5 : ℕ) ^ 3 < 2 ^ 7 ∧ (3 : ℕ) ^ 5 < 2 ^ 8 := by decide

end CollatzMoonshot.Sibling
