/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitHeightLaw

/-!
# The height line, all the way to `C*`

`heightLawUpTo_four` stops at `t = 4 size n` for reasons of bookkeeping: the letter-`1` tolerance
`1 / 100`, the number of scales `numScales = 4000`, and the horizon `21 / 5` in `GoodOdd` are fixed
numbers.  Letting them depend on `τ` should carry the line through every `τ < 1 / β`, and
`not_heightLawUpTo_of_gt` ends it there.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- **The height line through every `τ < 1 / β`.**  Believed, 90%. -/
theorem heightLawBelowThreshold : HeightLawBelowThreshold := by
  sorry

/-- **`C* = 1 / β` is the sharp end of the height line.** -/
theorem heightLawUpTo_iff {τ : ℝ} (hτ : τ * heightSlope ≠ 1) :
    HeightLawUpTo τ ↔ τ * heightSlope < 1 :=
  ⟨fun h => lt_of_le_of_ne (not_lt.mp fun hgt => not_heightLawUpTo_of_gt hgt h) hτ,
    fun h => heightLawBelowThreshold τ h⟩

/-- **First passage below `n^θ`, for every `0 < θ < 1`.**  From `heightLawBelowThreshold`.
Confidence 90%. -/
theorem firstPassage_sharp {θ ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    LogDens0 fun n : ℕ => ¬ (
      (∀ t : ℕ, (t : ℝ) ≤ ((1 - θ) / heightSlope - ε) * Nat.size n →
        (n : ℝ) ^ θ < (tstep^[t] n : ℝ)) ∧
      ∃ t : ℕ, (t : ℝ) ≤ ((1 - θ) / heightSlope + ε) * Nat.size n ∧
        (tstep^[t] n : ℝ) ≤ (n : ℝ) ^ θ) := by
  sorry

end CollatzMoonshot.Conjugacy
