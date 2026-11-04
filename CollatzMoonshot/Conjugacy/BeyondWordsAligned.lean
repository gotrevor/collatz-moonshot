/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.BeyondWordsLinearSharp

/-!
# Beyond-Terras uniformity on every aligned window `[q·2^j, (q+1)·2^j)`

`beyondTV j K` measures the first window `[0, 2^j)`.  For any aligned window the iterate identity
(`tstep_iterate_identity`, `traceWord_add_mul`) gives `T^j (r + q 2^j) = T^j r + 3^a q` on
`levelSet j a`, so per slice the residues mod `2^K` are the first window's residues shifted by a
slice constant; every per-slice residue-sum bound is shift-invariant (reindex `c`), and both
growing-depth theorems hold verbatim for every aligned window.  Ensemble statements over the
window's starts; nothing about any individual orbit.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- The beyond-Terras residue count on the aligned window `[A, A + 2^j)`. -/
def beyondCountAt (A j K c : ℕ) : ℕ :=
  ((Finset.Ico A (A + 2 ^ j)).filter (fun r => tstep^[j] r % 2 ^ K = c)).card

/-- Total-variation distance to uniform on `ℤ/2^K` of the beyond-Terras residues of the aligned
window `[A, A + 2^j)`. -/
noncomputable def beyondTVAt (A j K : ℕ) : ℝ :=
  ∑ c ∈ Finset.range (2 ^ K), |(beyondCountAt A j K c : ℝ) / 2 ^ j - 1 / 2 ^ K|

/-- Teeth: the window at `A = 0` is the original statistic. -/
theorem beyondTVAt_zero (j K : ℕ) : beyondTVAt 0 j K = beyondTV j K := by
  sorry

/-- **Frozen (2026-11-04).**  Log-depth uniformity on every aligned window, unconditional. -/
theorem beyondWordsUniformLogAt :
    ∀ C : ℝ, ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ C * Real.logb 2 j →
      ∀ q : ℕ, beyondTVAt (q * 2 ^ j) j K ≤ ε := by
  sorry

/-- **Frozen (2026-11-04).**  Linear-depth uniformity on every aligned window, every
`κ < (log₂ 3)/2`, from the sliced Proposition 1.14 node. -/
theorem beyondWordsUniformLinearAt_of_sliceOscDecay_sharp (h : SliceOscDecay) (κ : ℝ)
    (hκ : κ < Real.logb 2 3 / 2) :
    ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ κ * j →
      ∀ q : ℕ, beyondTVAt (q * 2 ^ j) j K ≤ ε := by
  sorry

end CollatzMoonshot.Conjugacy
