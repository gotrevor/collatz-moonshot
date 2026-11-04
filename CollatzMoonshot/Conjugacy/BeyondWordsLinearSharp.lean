/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.BeyondWordsLinear

/-!
# The linear-depth edge at its natural limit: every `κ < (log₂ 3)/2`

`beyondWordsUniformLinear_of_sliceOscDecay` reaches depth `K ≤ j/8` from the node `SliceOscDecay`
with the fixed choice `m = ⌊a/2⌋` on the band `j ≤ 4a ≤ 11j/5`.  The per-slice bound
`sum_norm_levelSum_resInd_le` is general in `m`: on a slice `a` the residue sums are
`≤ 2 levelOsc j a m + 2^K 3^{m−a} card` for every `m ≤ a`.  Taking the band `|a − j/2| ≤ δ j`
(Chebyshev, `sum_oddDeviation_sq_real`: the complement has `≤ 2^j/(4 δ² j)` starts) and
`m = a − ⌈K log₃ 2 + log₃(4/ε)⌉`, the second term is `≤ ε/4` and `m ≥ j((1/2 − δ) − κ log₃ 2) −
O(1) → ∞` whenever `κ < (1/2 − δ) log₂ 3`, so the node (any exponent `A ≥ 1`) kills the first
term.  Hence uniformity to every linear depth `κ j` with `κ < (log₂ 3)/2 ≈ 0.792`.

Ensemble statement over all `j`-bit starts; nothing about any individual orbit.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- **Frozen (2026-11-04).**  From the sliced Proposition 1.14 node, beyond-Terras uniformity
holds to every linear depth `K ≤ κ j` with `κ < (log₂ 3)/2`. -/
theorem beyondWordsUniformLinear_of_sliceOscDecay_sharp (h : SliceOscDecay) (κ : ℝ)
    (hκ : κ < Real.logb 2 3 / 2) : BeyondWordsUniformLinear κ := by
  sorry

end CollatzMoonshot.Conjugacy
