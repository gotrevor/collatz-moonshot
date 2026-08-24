import CollatzMoonshot.FrontA.BackwardThreeQuarters
import CollatzMoonshot.FrontA.BackwardTwoThirdsStopping

/-!
# Pinned end-to-end target: exponent-3/4 stopping growth

This file pins the final public corollary for the exponent-3/4 backward-tree
pipeline.  Completing it requires the exact real-rpow renewal layer, finite
value-injective child sets, the repeat-or-stopping frontier recursion, cycle
elimination, and the explicit potential min/max cardinal calculation.

The target statement and constants must not be weakened.  Supporting material
should be split into BackwardThreeQuartersRenewal.lean and this stopping module,
then both modules should be imported from CollatzMoonshot.lean.
-/

namespace CollatzMoonshot.FrontA

open scoped Real

/-- A five-height state paired with its odd endpoint. -/
abbrev ThreeQuartersNode := Fin 5 × ℕ

/-- **Pinned exponent-3/4 stopping-cardinality target.**  Assuming no
nontrivial cycle, every odd unit root `2 ≤ d ≤ H` has a finite value-injective
first-exit frontier with the explicit `(H/d)^(3/4)` cardinal lower bound.
Every endpoint lies in `(H, 2^23 H)` and is reached within `[d, 2^25 H]`. -/
theorem threeQuarters_stopping_card_bound (hnc : NoNontrivialCycle)
    {d H : ℕ} (hd : 2 ≤ d) (hdodd : d % 2 = 1) (hd3 : ¬3 ∣ d) (hdH : d ≤ H) :
    ∃ S : Finset ThreeQuartersNode,
      (1000000 : ℝ) <
        (S.card : ℝ) *
          (19334101 * ((d : ℝ) / (H : ℝ)) ^ (3 / 4 : ℝ)) ∧
      (∀ s ∈ S, ∀ t ∈ S, s.2 = t.2 → s = t) ∧
      ∀ s ∈ S, H < s.2 ∧ s.2 < 2 ^ 23 * H ∧
        ReachesInBand d (2 ^ 25 * H) s.2 := by
  sorry

end CollatzMoonshot.FrontA
