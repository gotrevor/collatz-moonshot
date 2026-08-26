/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Rigidity.Furstenberg

/-!
# Furstenberg's ×2×3 topological rigidity — DISCHARGED (2026-08-26)

Formerly a THEOREM-grade axiom (planted 2026-07-20); now a theorem.  The proof
lives in `Rigidity/Furstenberg.lean` — Boshernitzan's elementary route as
presented in Manners, arXiv:1305.1514 §4 — and carries the standard trust base
only.  The name and statement are unchanged so existing references stay valid.
-/

namespace CollatzMoonshot.Assumed

/-- **[DISCHARGED — proved in `Rigidity/Furstenberg.lean`]** Furstenberg's
topological ×2×3 rigidity: a closed subset of the circle carried into itself by
both doubling and tripling is finite or the whole circle.

Provenance: Furstenberg, *Disjointness in ergodic theory, minimal sets, and a
problem in Diophantine approximation* (1967), Theorem IV.1.  The finite sets
are the rational cycles; "2 and 3 don't share digit structure" in topological
form.  Axiomatized 2026-07-20, proved 2026-08-26 via the general
`Furstenberg.isClosed_invariant_finite_or_univ`.

⚠️ Keep this apart from Furstenberg's ×2×3 **measure** conjecture (the atomic-
or-Lebesgue classification of jointly invariant measures WITHOUT an entropy
hypothesis), which is OPEN - that one may never be an axiom here under the
THEOREM tier.  Rudolph-Johnson (positive entropy) covers the known part; see
`Rigidity/Circle.lean`. -/
theorem furstenberg_topological_rigidity :
    ∀ S : Set UnitAddCircle, IsClosed S →
      Set.MapsTo circleDouble S S → Set.MapsTo circleTriple S S →
      S.Finite ∨ S = Set.univ := by
  intro S hS h2 h3
  have h2' : Set.MapsTo ((2 : ℕ) • · : UnitAddCircle → UnitAddCircle) S S := by
    intro x hx
    show (2 : ℕ) • x ∈ S
    rw [two_nsmul]
    exact h2 hx
  have h3' : Set.MapsTo ((3 : ℕ) • · : UnitAddCircle → UnitAddCircle) S S := by
    intro x hx
    show (3 : ℕ) • x ∈ S
    have h3x : (3 : ℕ) • x = x + x + x := by
      rw [show (3 : ℕ) = 2 + 1 by rfl, add_nsmul, two_nsmul, one_nsmul]
    rw [h3x]
    exact h3 hx
  exact Furstenberg.isClosed_invariant_finite_or_univ (by norm_num) (by norm_num)
    Furstenberg.multIndep_two_three hS h2' h3'

end CollatzMoonshot.Assumed
