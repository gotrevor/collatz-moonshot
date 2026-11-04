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
`firstPassage_sharp` at `θ = min (1 / 2) (β ε / 2)`, since `1 / β − ε ≤ (1 − θ) / β − ε / 2`; the
starts with `f n > n^θ` are bounded. -/
theorem timeLaw_lower {f : ℕ → ℝ} (hf : ∀ θ : ℝ, 0 < θ → ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ θ)
    {ε : ℝ} (hε : 0 < ε) :
    LogDens0 fun n : ℕ =>
      ∃ t : ℕ, (t : ℝ) ≤ (1 / heightSlope - ε) * Nat.size n ∧ (tstep^[t] n : ℝ) ≤ f n := by
  have hβ := heightSlope_pos
  set θ : ℝ := min (1 / 2) (heightSlope * ε / 2) with hθdef
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hθε : θ / heightSlope ≤ ε / 2 := by
    rw [div_le_iff₀ hβ]
    have := min_le_right (1 / 2 : ℝ) (heightSlope * ε / 2)
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hf θ hθ)
  refine ((firstPassage_sharp hθ hθ1 (half_pos hε)).or
    (logDens0_of_bdd (B := N) fun n (h : ¬ f n ≤ (n : ℝ) ^ θ) => ?_)).mono fun n hn => ?_
  · by_contra hlt
    exact h (hN n (not_le.mp hlt).le)
  · obtain ⟨t, ht, hft⟩ := hn
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨⟨hfirst, -⟩, hfn⟩ := hcon
    have hsn : (0 : ℝ) ≤ Nat.size n := Nat.cast_nonneg _
    have hc : 1 / heightSlope - ε ≤ (1 - θ) / heightSlope - ε / 2 := by
      have : (1 - θ) / heightSlope = 1 / heightSlope - θ / heightSlope := by ring
      linarith
    have := hfirst t (le_trans ht (mul_le_mul_of_nonneg_right hc hsn))
    linarith

end CollatzMoonshot.Conjugacy
