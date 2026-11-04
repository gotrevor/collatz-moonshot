/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.BeyondWords

/-!
# Beyond-Terras words over a fixed dyadic block

`BeyondWordsUniform` takes `n < 2^b`.  Here `n` runs over a block `[α 2^b, (α + 1) 2^b)` for fixed
`α`.  Then `T^b (r + α 2^b) = T^b r + α 3^s`, `s` the odd count of `r`
(`tstep_iterate_add_mul_two_pow`), and on the slice `s = a` the shift is a constant.  So the residue
test on the block is a residue test on the slice, at the shifted residue `shiftRes K c α a`.  The
slice bound `eventually_norm_levelSum_le` is uniform over observables of the given weight, and
`layeredWeight_resInd` is uniform in the residue, so the slices sum as in `BeyondWordsUniform`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- The starts in block `α` (`n = r + α 2^b`, `r < 2^b`) whose `b`-th iterate is `c mod 2^K`. -/
def blockCount (b α K c : ℕ) : ℕ :=
  ((Finset.range (2 ^ b)).filter fun r => tstep^[b] (r + α * 2 ^ b) % 2 ^ K = c).card

/-- **Node.**  Over each fixed block, `T^b n mod 2^K` is uniform as `b → ∞`.  At `α = 0` this is
`BeyondWordsUniform`. -/
def BlockWordsUniform : Prop :=
  ∀ α K c : ℕ, c < 2 ^ K →
    Tendsto (fun b : ℕ => (blockCount b α K c : ℝ) / 2 ^ b) atTop (𝓝 (1 / 2 ^ K))

/-- The residue `y` must have mod `2^K` for `y + α 3^a` to be `c`: `(2^K − 1) s ≡ −s`. -/
def shiftRes (K c α a : ℕ) : ℕ := (c + (2 ^ K - 1) * (α * 3 ^ a)) % 2 ^ K

theorem shiftRes_lt (K c α a : ℕ) : shiftRes K c α a < 2 ^ K :=
  Nat.mod_lt _ (by positivity)

/-- On the slice `a`, the block's residue test is the shifted residue test on `T^b r`. -/
theorem block_test_iff (b α K c a r : ℕ) (hc : c < 2 ^ K) (hr : r ∈ levelSet b a) :
    tstep^[b] (r + α * 2 ^ b) % 2 ^ K = c ↔ tstep^[b] r % 2 ^ K = shiftRes K c α a := by
  sorry

/-- The centred block count is a sum over slices of centred residue indicators. -/
theorem sum_block_eq (b α K c : ℕ) (hc : c < 2 ^ K) :
    (blockCount b α K c : ℂ) - 2 ^ b * ((2 : ℂ) ^ K)⁻¹ =
      ∑ a ∈ Finset.range (b + 1), ∑ r ∈ levelSet b a,
        resInd K (shiftRes K c α a) (tstep^[b] r) := by
  sorry

/-- Central slices by the hypothesis, the others by their cardinality.  The observable may vary with
the slice, unlike in `norm_sum_range_le_of_levelSum`. -/
theorem norm_sum_slices_le (j : ℕ) (f : ℕ → ℕ → ℂ) (hf1 : ∀ a y, ‖f a y‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hslice : ∀ a, j ≤ 4 * a → a ≤ 11 * j / 20 →
      ‖∑ r ∈ levelSet j a, f a (tstep^[j] r)‖ ≤ ε * (levelSet j a).card) :
    ‖∑ a ∈ Finset.range (j + 1), ∑ r ∈ levelSet j a, f a (tstep^[j] r)‖ ≤
      ε * 2 ^ j + (outOddSet j).card := by
  sorry

/-- **Block words are uniform**, from slice character decay. -/
theorem blockWordsUniform_of_sliceCharDecay (h : SliceCharDecay) : BlockWordsUniform := by
  sorry

/-- Unconditional, through the Sec7P node. -/
theorem blockWordsUniform : BlockWordsUniform :=
  blockWordsUniform_of_sliceCharDecay (sliceCharDecay_of_pascalDampingDecay pascalDampingDecay)

end CollatzMoonshot.Conjugacy
