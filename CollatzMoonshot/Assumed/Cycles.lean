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

/-- **[ASSUMED - published theorem]** Any cycle outside the trivial one has period
at least `17,087,915`.

Provenance: Eliahou (1993), *The 3x+1 problem: new lower bounds on nontrivial
cycle lengths*, via the continued-fraction structure of `log₂ 3` plus the
computational frontier of its day.  Later work (Simons-de Weger 2005 and
successors, plus the modern verification frontier) pushes far past this; the
number here is the classical, conservative bound - verify before citing a
sharper one externally.

Stated for ALL periods, not just the minimal one: any period is a multiple of the
minimal period, so the bound transfers. -/
axiom eliahou_min_cycle_length :
    ∀ n m : ℕ, 1 ≤ n → 0 < m → step^[m] n = n →
      (n = 1 ∨ n = 2 ∨ n = 4) ∨ 17087915 ≤ m

end CollatzMoonshot.Assumed
