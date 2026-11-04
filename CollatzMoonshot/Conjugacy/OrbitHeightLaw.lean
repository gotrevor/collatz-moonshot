/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLaw

/-!
# The height line and the first passage

`orbitWordLaw_of_le_four` counts letters.  Its proof gives more, since `GoodOdd` controls every prefix
of the first `4.2 size n` letters and `height_identity` reads the height off the odd letters: almost
every start in logarithmic density follows the line `log₂ n − β t`, `β = 1 − log₂ 3 / 2`, through
`t = 4 size n` (`heightLawUpTo_four`).  First passage below `n^θ` follows (`firstPassage_law`), at
`t ≈ (1 − θ) size n / β`.

The line must end at `1 / β = C*`, where it would go negative (`not_heightLawUpTo_of_gt`).  Reaching
`C*` from below is the node `HeightLawBelowThreshold`.

`StageWordLaw` is the same orbit statement over one stage in place of logarithmic density.  It gives
normality (`normal_of_stageWordLaw`), and it is what logarithmic density does not reach (research note
§16).

`experiments/conjugacy/height_line.py` compares the line and the passage times with data out to
`k = 20000`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- The slope of the height line, per step: `β = 1 − log₂ 3 / 2`. -/
noncomputable def heightSlope : ℝ := 1 - Real.logb 2 3 / 2

/-- The orbit of `n` leaves the height line by more than `ε size n`, at some `t ≤ τ size n`. -/
def BadHeight (τ ε : ℝ) (n : ℕ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ τ * Nat.size n ∧
    ε * Nat.size n < |Real.logb 2 (tstep^[t] n) - (Real.logb 2 n - heightSlope * t)|

/-- **The height law through `τ size n`.**  Almost every start in logarithmic density stays within
`ε size n` of the height line, for every `ε > 0`. -/
def HeightLawUpTo (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → LogDens0 (BadHeight τ ε)

/-- **The height line through `t = 4 size n`.**  From `goodOdd_whp` at `u = [true]`, `height_identity`
and the even reduction.  `heightCorr` is small since the line keeps the orbit above `n^(1/10)`.
Confidence 90%. -/
theorem heightLawUpTo_four : HeightLawUpTo 4 := by
  sorry

/-- **The line ends at `C* = 1 / β`.**  Past it the line goes negative while heights stay `≥ 0`, so every
large start is bad.  Confidence 95%. -/
theorem not_heightLawUpTo_of_gt {τ : ℝ} (hτ : 1 < τ * heightSlope) : ¬ HeightLawUpTo τ := by
  sorry

/-- **Node: the height line all the way to `C*`.**  The chain of `dTV_chain` with a number of scales
depending on `τ`, in place of the fixed `numScales`.  Believed, 85%. -/
def HeightLawBelowThreshold : Prop :=
  ∀ τ : ℝ, τ * heightSlope < 1 → HeightLawUpTo τ

/-- **First passage below `n^θ`.**  For `θ` above `1 − 4β ≈ 0.17`, almost every start in logarithmic
density stays above `n^θ` until `((1 − θ) / β − ε) size n` steps, and has been at or below it by
`((1 − θ) / β + ε) size n`.  From `heightLawUpTo_four`.  Confidence 90%. -/
theorem firstPassage_law {θ ε : ℝ} (hθ : 1 - 4 * heightSlope < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    LogDens0 fun n : ℕ => ¬ (
      (∀ t : ℕ, (t : ℝ) ≤ ((1 - θ) / heightSlope - ε) * Nat.size n →
        (n : ℝ) ^ θ < (tstep^[t] n : ℝ)) ∧
      ∃ t : ℕ, (t : ℝ) ≤ ((1 - θ) / heightSlope + ε) * Nat.size n ∧
        (tstep^[t] n : ℝ) ≤ (n : ℝ) ^ θ) := by
  sorry

open Classical in
/-- **Node: the orbit word law over one stage.**  For every word `u` and `δ > 0`, the bad starts are a
vanishing fraction of the `k`-bit integers.  Stronger than `OrbitWordLaw`, which averages stages.
Open.  False for `C ≥ 5` (`not_stageWordLaw_of_five_le`). -/
def StageWordLaw (C : ℕ) : Prop :=
  ∀ (u : List Bool) (δ : ℝ), 0 < δ → Tendsto
    (fun k : ℕ => (((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (BadStart C u δ)).card : ℝ) / 2 ^ (k - 1))
    atTop (𝓝 0)

/-- **The stage law gives normality.**  Through `normal_of_stage_bound`: a good start contributes
`δ C k` to the sum over offsets, and each bad start at most `C k`.  Confidence 85%. -/
theorem normal_of_stageWordLaw (C : ℕ) (hC : 1 ≤ C) (h : StageWordLaw C) :
    Normal (collatzChampernowne C) := by
  sorry

/-- Above the threshold the stage law fails, since `𝒞_C` is not normal. -/
theorem not_stageWordLaw_of_five_le (C : ℕ) (hC : 5 ≤ C) : ¬ StageWordLaw C := fun h =>
  not_normal_of_five_le C hC (normal_of_stageWordLaw C (by omega) h)

end CollatzMoonshot.Conjugacy
