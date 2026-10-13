/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalConstant

/-!
# The window densities converge to `minimaConstant` (Sparre Andersen)

Target for a treadmill (`KICKOFF-2026-10-13-amusical-spitzer.md`): `windowDensityLimit`, after
which `orbitMin_density_le_minimaConstant` is unconditional.  The duality half is a termwise
identity: forward survival at time `k` and backward non-survival use the same binomial index set
`{o : 2^(k+o) < 3^k}`, with weights `C(k,o) 2^-k · 2^(k+o) 3^-k = C(k,o) 2^o 3^-k` on both sides.
The real content is Sparre Andersen's theorem for the two multiplicative walks.
-/

namespace CollatzMoonshot.Amusical

/-- **Target (treadmill).**  `fwdSurv L * bwdSurv L → minimaConstant`. -/
theorem windowDensityLimit : WindowDensityLimit := by
  sorry

open Classical in
/-- Orbit minima have upper density at most `minimaConstant ≈ 0.049780`. -/
theorem orbitMin_density_le_minimaConstant' {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X ≤ minimaConstant + ε :=
  orbitMin_density_le_minimaConstant windowDensityLimit hε

end CollatzMoonshot.Amusical
