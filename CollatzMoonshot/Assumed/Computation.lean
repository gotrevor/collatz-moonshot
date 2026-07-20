/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Basic

/-!
# Assumed: the computational verification frontier

Tier: THEOREM-grade (massive, replicated computation; not a formal proof anywhere).
-/

namespace CollatzMoonshot.Assumed

/-- **[ASSUMED - computation]** Every `n ≤ 2⁶⁸` reaches `1`.

Provenance: Bařina's distributed convergence verification (~2020) reached `2⁶⁸`;
per the `papers/eliahou-1993-summary.md` fact-check (2026-07-20), the frontier is
now `2⁷¹` (Bařina, J. Supercomputing 2025).  `2⁶⁸` stays as the conservative
floor here - bump only with firsthand verification.

This is exactly the kind of fact an investigatory repo assumes: replicated,
believed by everyone, and formalizing it honestly would mean certifying a
planet-scale computation - a project in itself, orthogonal to the moonshot. -/
axiom collatz_verified_up_to_two_pow_68 :
    ∀ n : ℕ, 1 ≤ n → n ≤ 2 ^ 68 → ReachesOne n

end CollatzMoonshot.Assumed
