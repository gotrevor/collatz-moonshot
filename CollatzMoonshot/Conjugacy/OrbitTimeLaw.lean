/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitHeightSharp

/-!
# The time law

Tao's `tao_collatz` says that almost every start in logarithmic density gets below `f n`, for any
`f → ∞`, and carries no time.  Here is the time: `(1 / β + o(1)) size n` steps of `tstep`, with
`β = 1 − log₂ 3 / 2` (`timeLaw_upper`), and for slowly growing `f` no sooner (`timeLaw_lower`).

This is the stochastic model's total stopping time `C* size n`, as far as `f → ∞` reaches.  It says
nothing about reaching `1`.

`experiments/conjugacy/time_law.py` compares it with data out to `k = 20000`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- **Within `(1 / β + ε) size n` steps the orbit is below `f n`.**  The chain over a number of scales
growing with `x`, down to a large constant `X`, with exceptions summing to `g X → 0`.  Believed, 85%. -/
theorem timeLaw_upper {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    LogDens0 fun n : ℕ =>
      ¬ ∃ t : ℕ, (t : ℝ) ≤ (1 / heightSlope + ε) * Nat.size n ∧ (tstep^[t] n : ℝ) ≤ f n := by
  sorry

/-- **For `f` below every power of `n`, not within `(1 / β − ε) size n` steps.**  From
`firstPassage_sharp`.  Confidence 90%. -/
theorem timeLaw_lower {f : ℕ → ℝ} (hf : ∀ θ : ℝ, 0 < θ → ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ θ)
    {ε : ℝ} (hε : 0 < ε) :
    LogDens0 fun n : ℕ =>
      ∃ t : ℕ, (t : ℝ) ≤ (1 / heightSlope - ε) * Nat.size n ∧ (tstep^[t] n : ℝ) ≤ f n := by
  sorry

end CollatzMoonshot.Conjugacy
