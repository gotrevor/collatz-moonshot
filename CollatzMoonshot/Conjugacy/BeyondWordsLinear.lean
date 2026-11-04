/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.BeyondWords
import CollatzMoonshot.Conjugacy.Bridge3

/-!
# Beyond-Terras uniformity at growing depth: logarithmic (unconditional) and linear (one node)

`BeyondWords.lean` proves that for every fixed `K` the residues `T^j r mod 2^K`, `r < 2^j`, are
asymptotically uniform (`beyondWordsUniform`).  This file asks how far past the Terras horizon
that uniformity reaches when `K` grows with `j`, measured in total variation:

    beyondTV j K = Σ_{c < 2^K} |beyondCount j K c / 2^j − 2^{−K}|.

* **Logarithmic depth, unconditional** (`beyondWordsUniformLog`): for every `C`, the first
  `C · log₂ j` letters past the horizon are jointly uniform.  The proof is the C1 pipeline of
  `SliceFourierGeneral.lean` run with its rate kept: on a slice `levelSet j a` in the window the
  centred residue count is `≤ 4(a+1) · C_A · j^{−A} · card` plus a sub-slice tail `≤ C a 3^{−j/12}
  card`, uniformly in `K` and `c` (`layeredWeight_resInd`, `SliceCharDecay`); summing over the
  `2^K = j^{C}` residues costs `j^C`, paid by `A = C + 2`; slices outside the window are
  `outOddSet j`, of size `O(2^j / j)`, and contribute at most twice their share to the TV sum.

* **Linear depth, one node** (`beyondWordsUniformLinear_of_sliceOscDecay`): the slice analogue
  of Tao 2019 Proposition 1.14 (`SliceOscDecay`: the oscillation of the slice law above the
  3-adic scale `m` is `≤ C m^{−A} · card`, for all `1 ≤ m ≤ a` in the window) gives uniformity
  to depth `K ≤ j/8`.  Mechanism: above scale `m` the slice law is within `levelOsc j a m` of a
  law that is uniform on every fibre `{c + 3^m t : t < 3^{a−m}}`; each fibre is an arithmetic
  progression with odd step, so its residues mod `2^K` are uniform up to `2^K / 3^{a−m}` per
  fibre; with `m = ⌊a/2⌋` and `a ≥ j/4` this is `≤ 2^{K − 0.198 j}`, which vanishes for
  `K ≤ j/8`.  The node implies `TruncatedSyracMixing` (`Bridge3.lean`) at once.  Its input,
  the sliced Proposition 1.17, is the theorem `sliceCharDecay`; the edge
  `SliceCharDecay → SliceOscDecay` is Tao's §6 for the sliced law and is NOT attempted here.

Both headline theorems are ensemble statements over all `j`-bit starts.  They say nothing about
any individual orbit, hence nothing about the Collatz conjecture.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology

/-- Total-variation distance, at depth `K`, between the beyond-Terras residues `T^j r mod 2^K`
over `r < 2^j` and the uniform distribution on `ℤ/2^K`. -/
noncomputable def beyondTV (j K : ℕ) : ℝ :=
  ∑ c ∈ Finset.range (2 ^ K), |(beyondCount j K c : ℝ) / 2 ^ j - 1 / 2 ^ K|

/-- **Node (frozen): the sliced Tao Proposition 1.14.**  On every slice in the window
`j ≤ 5a ≤ 3j` and at every 3-adic scale `1 ≤ m ≤ a`, the oscillation of the slice law above
scale `m` is a `C_A m^{−A}` fraction of the slice.  Its input, the sliced Proposition 1.17, is
the theorem `sliceCharDecay`; the edge is Tao's §6 argument for the sliced law.  Confidence
75% true; the probe is the exact `levelOsc` table (`experiments/conjugacy/`). -/
def SliceOscDecay : Prop :=
  ∀ A > (0 : ℝ), ∃ C > (0 : ℝ), ∀ j a m : ℕ, 1 ≤ m → m ≤ a → j ≤ 5 * a → 5 * a ≤ 3 * j →
    levelOsc j a m ≤ C * (m : ℝ) ^ (-A) * (levelSet j a).card

/-- **Linear-depth uniformity.**  For every `ε`, eventually in `j`, every depth `K ≤ κ j` has
`beyondTV j K ≤ ε`. -/
def BeyondWordsUniformLinear (κ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ κ * j → beyondTV j K ≤ ε

/-- **Logarithmic-depth uniformity.**  For every `C` and `ε`, eventually in `j`, every depth
`K ≤ C log₂ j` has `beyondTV j K ≤ ε`. -/
def BeyondWordsUniformLog : Prop :=
  ∀ C : ℝ, ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ C * Real.logb 2 j →
    beyondTV j K ≤ ε

/-- **Edge (elementary).**  The sliced Proposition 1.14 gives the truncated mixing node of
`Bridge3.lean`: take `m = ⌊a/2⌋`. -/
theorem truncatedSyracMixing_of_sliceOscDecay (h : SliceOscDecay) : TruncatedSyracMixing := by
  sorry

/-- **Edge: linear depth from the sliced Proposition 1.14** (the fibre-progression argument of
the module docstring, with `m = ⌊a/2⌋` and the `outOddSet` tail). -/
theorem beyondWordsUniformLinear_of_sliceOscDecay (h : SliceOscDecay) :
    BeyondWordsUniformLinear (1 / 8) := by
  sorry

/-- **Theorem (unconditional): logarithmic depth.**  The first `C log₂ j` letters past the
Terras horizon are jointly uniform, for every `C`. -/
theorem beyondWordsUniformLog : BeyondWordsUniformLog := by
  sorry

/-- Consistency: logarithmic-depth uniformity recovers the fixed-`K` statement of
`BeyondWords.lean`. -/
theorem beyondWordsUniform_of_log (h : BeyondWordsUniformLog) : BeyondWordsUniform := by
  sorry

end CollatzMoonshot.Conjugacy
