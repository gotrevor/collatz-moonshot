/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalEscape

/-!
# No amusical itinerary is base-3 normal (research §54)

Label each step of a `U`-orbit by its branch (`stepSym`: 0 even, 1 for `4n + 1`, 2 for `4n + 3`).
The "normal" agent (2026-10-15) asked whether the itinerary of an infinite orbit, read as a base-3
real, can be normal.  It cannot: normality would give the even label frequency `1/3`.

* An aperiodic orbit cannot have even-frequency `1/3 < log₂(4/3)`: such an orbit spends more than
  `log₂ 3` bits per step and falls (`periodic_of_evenFrequency_lt`, `AmusicalEscape.lean`).
* A cycle cannot have even-frequency `1/3` either.  Around a cycle of length `p` with `E` even
  steps the product of the step ratios is 1, so `3^p · ∏_{odd x} (1 + ε(x)/(3x)) = 2^{2p − E}`.
  At `E = p/3` the odd factors must average at least `(2^{5/3}/3)^{3/2} ≈ 1.089`, forcing odd cycle
  elements `≤ 3`; the only such cycles are `{1}` (frequency 0) and `{2, 3}` (frequency `1/2`).

* `not_tendsto_evenFrequency_third`: for every positive integer, the even-label frequency of its
  forward itinerary does not tend to `1/3`.  So no positive integer's itinerary is base-3 normal.
-/

namespace CollatzMoonshot.Amusical

/-- **Target.**  No positive integer's forward `U`-itinerary has even-label frequency tending to
`1/3`; in particular, read in base 3, no such itinerary is normal. -/
theorem not_tendsto_evenFrequency_third (m : ℤ) (hm : 0 < m) :
    ¬ Filter.Tendsto (fun k : ℕ =>
      (((Finset.range k).filter fun j => stepSym (amusical^[j] m) = 0).card : ℝ) / k)
      Filter.atTop (nhds (1 / 3)) := by
  sorry

end CollatzMoonshot.Amusical
