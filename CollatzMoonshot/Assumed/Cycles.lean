/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Basic

/-!
# Assumed: cycle-length lower bounds

Tier: THEOREM-grade (published proofs, unformalized).  This is Front B territory
(`APPROACHES.md`, Approach 3): Baker linear forms + the continued fraction of
`log₂ 3` make cycle lengths astronomically large.
-/

namespace CollatzMoonshot.Assumed

/-- **[ASSUMED - published theorem]** Any cycle of `step` outside the trivial one
has period at least `27,869,189`.

Provenance: Eliahou (1993), *The 3x+1 problem: new lower bounds on nontrivial
cycle lengths* (Discrete Math. 118; PDF + summary in `papers/`), via the product
identity `∏ (3 + 1/n) = 2^k` over odd cycle elements plus the continued-fraction
structure of `log₂ 3` and the 1993 verification cutoff `2⁴⁰`.  ⚠️ Map bookkeeping:
Eliahou's headline `17,087,915` counts iterations of the SHORTCUT map
(`(3n+1)/2` in one step), with `10,781,274` odd steps; this repo's `step` takes
the odd move in two steps, so the corresponding bound here is the sum,
`27,869,189`.  The modern frontier (Hercher 2023 + Bařina's `2⁷¹` verification)
pushes this to ~`3.6 × 10¹¹` for this map - not adopted pending firsthand
verification of those papers.

Stated for ALL periods, not just the minimal one: any period is a multiple of the
minimal period, so the bound transfers. -/
axiom eliahou_min_cycle_length :
    ∀ n m : ℕ, 1 ≤ n → 0 < m → step^[m] n = n →
      (n = 1 ∨ n = 2 ∨ n = 4) ∨ 27869189 ≤ m

end CollatzMoonshot.Assumed
