import CollatzMoonshot.FrontA.BackwardThreeQuartersStopping

/-!
# Pinned end-to-end target: exponent-4/5 stopping growth

This file pins the final public corollary for the depth-8 correlated
exponent-4/5 backward-tree certificate.  Completing it requires freezing and
formalizing the 21,870-state local potential, then delivering its exact-real
renewal and recursive stopping consequences.  The statement and constants
below must not be weakened.
-/

namespace CollatzMoonshot.FrontA

open scoped Real

abbrev FourFifthsNode := Fin 5 × ℕ

/-- **Pinned exponent-4/5 stopping-cardinality target.**  Assuming no
nontrivial cycle, every odd unit root `2 ≤ d ≤ H` has a finite value-injective
first-exit frontier with the explicit `(H/d)^(4/5)` cardinal lower bound.
Every endpoint lies in `(H, 2^23 H)` and is reached within `[d, 2^25 H]`. -/
theorem fourFifths_stopping_card_bound (hnc : NoNontrivialCycle)
    {d H : ℕ} (hd : 2 ≤ d) (hdodd : d % 2 = 1) (hd3 : ¬3 ∣ d) (hdH : d ≤ H) :
    ∃ S : Finset FourFifthsNode,
      (1000000 : ℝ) <
        (S.card : ℝ) *
          (41080952 * ((d : ℝ) / (H : ℝ)) ^ (4 / 5 : ℝ)) ∧
      (∀ s ∈ S, ∀ t ∈ S, s.2 = t.2 → s = t) ∧
      ∀ s ∈ S, H < s.2 ∧ s.2 < 2 ^ 23 * H ∧
        ReachesInBand d (2 ^ 25 * H) s.2 := by
  sorry

end CollatzMoonshot.FrontA
