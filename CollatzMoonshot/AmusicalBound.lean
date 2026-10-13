/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindow

/-!
# Orbit minima of the amusical permutation have upper density below `1/20`

`windowMinDensity 200` bounds the upper density of orbit minima by `δ₂₀₀ = fwdSurv 200 *
bwdSurv 200 = 0.0498876…`, just under `1/20` (the conjectured density is `0.049780`).  The
pattern sums have `2^200` terms, so `windowDensity_two_hundred_lt` needs a dynamic-programming
form of `fwdSurv` and `bwdSurv` (state: step and number of marked steps) proved equal to the
definitions, then an exact rational evaluation.  Plan: `KICKOFF-2026-10-13-amusical-bound.md`.
-/

namespace CollatzMoonshot.Amusical

/-- **Target (treadmill).**  `δ₂₀₀ < 1/20`.  Exact value `0.04988761510…`
(`scripts/amusical/window.py`-style lattice computation, 2026-10-13). -/
theorem windowDensity_two_hundred_lt : fwdSurv 200 * bwdSurv 200 < 1 / 20 := by
  sorry

open Classical in
/-- **Orbit minima have upper density below `1/20`**: eventually fewer than `X/20` of
`0, …, X-1` are orbit minima. -/
theorem orbitMin_density_lt_one_twentieth : ∀ᶠ X : ℕ in Filter.atTop,
    (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X < 1 / 20 := by
  set δ : ℝ := ((fwdSurv 200 * bwdSurv 200 : ℚ) : ℝ)
  have hδ : δ < 1 / 20 := by
    have h := windowDensity_two_hundred_lt
    have : ((fwdSurv 200 * bwdSurv 200 : ℚ) : ℝ) < ((1 / 20 : ℚ) : ℝ) := Rat.cast_lt.2 h
    simpa [δ] using this
  filter_upwards [orbitMin_density_le 200 (by linarith : (0 : ℝ) < (1 / 20 - δ) / 2)] with X hX
  linarith

end CollatzMoonshot.Amusical
