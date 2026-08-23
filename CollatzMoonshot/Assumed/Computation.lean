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

/-- **[ASSUMED - computation]** Every `n ≤ 2075 · 2⁶⁰ (≈ 2^71.02)` reaches `1`.

Provenance: Bařina, *Improved verification limit for the convergence of the
Collatz conjecture*, J. Supercomputing **81**, 810 (2025), DOI
10.1007/s11227-025-07337-0; completion (2025-01-15) checked firsthand on the
project page 2026-08-22 (see `papers/barina-2025-verification-limit.md`).
Compute-trust caveat: a replicated distributed computation, not a proof
artifact.  The `2⁶⁸` axiom above stays as the conservative floor with its own
provenance; downstream results choose their input, and `#print axioms` shows
which frontier each one stands on. -/
axiom collatz_verified_barina_2025 :
    ∀ n : ℕ, 1 ≤ n → n ≤ 2075 * 2 ^ 60 → ReachesOne n

end CollatzMoonshot.Assumed
