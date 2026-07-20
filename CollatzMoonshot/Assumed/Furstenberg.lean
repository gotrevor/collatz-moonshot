/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Rigidity.Circle

/-!
# Assumed: Furstenberg's ×2×3 topological rigidity

Tier: THEOREM-grade (published 1967, unformalized anywhere we know of).  This is
the entropy-free member of the 2⊥3 rigidity trinity, so unlike Rudolph-Johnson it
can be axiomatized without an opaque-entropy caveat.
-/

namespace CollatzMoonshot.Assumed

/-- **[ASSUMED - published theorem]** Furstenberg's topological ×2×3 rigidity: a
closed subset of the circle carried into itself by both doubling and tripling is
finite or the whole circle.

Provenance: Furstenberg, *Disjointness in ergodic theory, minimal sets, and a
problem in Diophantine approximation* (1967).  The finite sets are the rational
cycles; "2 and 3 don't share digit structure" in topological form.

⚠️ Keep this apart from Furstenberg's ×2×3 **measure** conjecture (the atomic-or-
Lebesgue classification of jointly invariant measures WITHOUT an entropy
hypothesis), which is OPEN - that one may never be an axiom here under the
THEOREM tier.  Rudolph-Johnson (positive entropy) covers the known part; see
`Rigidity/Circle.lean`. -/
axiom furstenberg_topological_rigidity :
    ∀ S : Set UnitAddCircle, IsClosed S →
      Set.MapsTo circleDouble S S → Set.MapsTo circleTriple S S →
      S.Finite ∨ S = Set.univ

end CollatzMoonshot.Assumed
