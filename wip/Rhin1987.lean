/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# [ASSUMED — published theorem] Rhin's 1987 effective linear-independence measure of `1, log2, log3`

This is the sole deep Diophantine input behind the interior two-block exclusion
(`sep_two_three` in `FrontA/PowSeparation.lean`, hence `b + d ≤ 5`).  A review lap proved the
inequality is **Baker-grade** (no elementary/`nlinarith` certificate can exist), and the exact
object needed is an effective irrationality measure of `log₂3` — a linear form in the two
logarithms `log 2`, `log 3`.

The sharpest unconditional, fully explicit (threshold-free) such measure is Rhin's:

> **Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, Séminaire de Théorie des
> Nombres (Paris 1985-86), Progress in Mathematics 71, Birkhäuser 1987, 155-164.**
> Proposition (verbatim): *"Soient `u₀, u₁, u₂` trois entiers tels que `H = max(|u₁|,|u₂|) ≥ 2`.
> Alors la forme `Λ = u₀ + u₁ log 2 + u₂ log 3` vérifie (7) `|Λ| ≥ H^{-13.3}`."*

Read firsthand 2026-08-24 (copy at `papers/rhin-1987-pade-mesures-effectives.pdf`); provenance and
the (separate, unusable-here) asymptotic `7.616` form are logged in
`ON-LINE-FINDINGS-2026-08-25-rhin-primary-source-verified.md` and the reference corpus note
`2026-08-24-log2-3-effective-irrationality-measure.md`.  🔑 `u₀` is **not** in the max; the
threshold really is `H ≥ 2`.

We state the immediate integer-exponent weakening `|Λ| ≥ H^{-14}` (since `H^{-13.3} ≥ H^{-14}` for
`H ≥ 1`), which is the directly-usable form; it is strictly implied by Rhin's `13.3`.

**Retirement path.**  This is a citation, not a permanent assumption.  The independent Rhin-lite
construction (`FrontA/RhinLite*.lean`, `FrontA/RhinLiteApprox.lean`) aims to *prove* a coarse
version (`rhinLiteLIMeasure`, `μ ≈ 7.9`) from first principles via Wu's `K = 1` structural
clearing, which would let this axiom be deleted (cf. how `Assumed/Furstenberg.lean` was retired).
Until then it is the honest, provenance-pinned input, exactly the doctrine used for the Hercher
cycle bound in `Assumed/Cycles.lean`.
-/

namespace CollatzMoonshot.Assumed

/-- **[ASSUMED — Rhin 1987]** Effective linear-independence measure of `1, log 2, log 3`.
For integers `u₀, u₁, u₂` with `H = max(|u₁|, |u₂|) ≥ 2`, the linear form
`Λ = u₀ + u₁·log2 + u₂·log3` satisfies `|Λ| ≥ 1/H^14`.

This is the integer-exponent (`14 ≥ 13.3`) weakening of Rhin's published `|Λ| ≥ H^{-13.3}`
(Progress in Math. 71 (1987), 155-164, Proposition (7); `H ≥ 2`, `u₀` excluded from the max). -/
axiom rhin_1987_log_two_three_measure :
    ∀ u₀ u₁ u₂ : ℤ, 2 ≤ max |u₁| |u₂| →
      1 / ((max |u₁| |u₂| : ℤ) : ℝ) ^ 14
        ≤ |(u₀ : ℝ) + u₁ * Real.log 2 + u₂ * Real.log 3|

end CollatzMoonshot.Assumed
