# HANDOFF 2026-08-31 — determinant node CONFIRMED nonzero; reduced to the real integral det

- **Branch:** `main`  **Tree:** clean after commit, not pushed.
- `lake build` green (8764 jobs).  `bash scripts/check-proof-debt.sh` = **one** disclosed sorry
  repo-wide: `RhinLiteApprox.lean:1160` (`rhinLite_integralMatrix_det_ne_zero`) — the node was
  RENAMED/relocated from `rhinLite_formMatrix_det_ne_zero` (now PROVED from it).

## What this lap did

### 1. Mandatory numeric sanity-check (exact Python integers) — DONE
`experiments/rhin_lite_det_check.py` builds `H_N` for the six-factor block subsequence `N = 2000t`
(spacing 2000) with pure Python bigints and computes the form determinant EXACTLY via the reduction
`det(B,A₁,A₂) = D_{N₀}D_{N₁}D_{N₂}·det(c_N, R₁, R₂)`, `R_i = A_i/D_N` = rational part of `∫ᵢ`.

**Result: the determinant is NONZERO** (`t₀=1`: `log₁₀|det(c_N,R₁,R₂)| ≈ 3570`; `t₀=0` 2×2 minor
`≈ 3692`).  The statement is TRUE — NOT refuted.  **BUT it is exponentially near-degenerate:**
`R₁(t)/R₂(t) = A₁(t)/A₂(t) ≈ log(3/2)/log(4/3) = 1.4094208…` to `≈ N` digits (t=1→2500, t=2→5000,
t=3→7500 identical digits), because `R_i = I_i − c_N θ_i ≈ −c_N θ_i` with `I_i = ∫ᵢ` tiny.  The
ratio *difference* across `t` is `~10^{−3812}` (t=1 vs 2).  So a coarse bound CANNOT separate `det`
from 0; nonzero-ness = strict monotonicity of `R₁(t)/R₂(t)`.  (See `PENDING_WORK.md` top section.)

### 2. Retired the `Classical.choose` opacity (Lean, trust-base clean)
- `rhinLite_forms_full` — strengthened bounded-forms package that ALSO carries the three structural
  equalities: `B = lcmUpto N·centralCoeff`, `lcmUpto N·∫ᵢ = Aᵢ + B·log(·)`.
- `rhinLiteA₁/A₂/B` now defined off `rhinLite_forms_full`; `rhinLiteFD_spec` re-derived unchanged
  (all downstream consumers untouched); `rhinLiteFD_eq` exposes the equalities.
- `rhinLite_row_relations` — the per-row real form `B = D·c`, `A₁ = D·I₁ − B·log(3/2)`,
  `A₂ = D·I₂ − B·log(4/3)`.

### 3. Column-reduction identity PROVED (the crux decomposition)
- `rhinLiteCentral/rhinLiteI₁/rhinLiteI₂`, `rhinLiteIntegralMatrix` (real rows `(c_N, I₁, I₂)`).
- `rhinLite_formMatrix_det_cast` (PROVED, trust-base clean): `((formMatrix).det : ℝ) =
  D_{N₀}D_{N₁}D_{N₂}·(integralMatrix).det`.  The unimodular real column op `(B,A₁,A₂) ↦
  (B, A₁+B log(3/2), A₂+B log(4/3)) = (B, D I₁, D I₂)` — log terms cancel by `ring` (after
  `det_fin_three` on both sides; rewrite the `A`s BEFORE the `B`s so no `B` survives).
- `rhinLite_formMatrix_det_ne_zero` (PROVED from the node below): `det ≠ 0` follows from the real
  integral det ≠ 0 times the nonzero denominator product.

## The SOLE remaining obligation (renamed)

`rhinLite_integralMatrix_det_ne_zero (t₀) : (rhinLiteIntegralMatrix t₀).det ≠ 0`
— the 3×3 REAL determinant of `(c_N, I₁, I₂)` over `t₀, t₀+1, t₀+2` is nonzero.  This is the genuine
analytic core.  **Attack (next laps):** expand `det = c_{N₂}·(I₁(t₀)I₂(t₀+1)−I₂(t₀)I₁(t₀+1)) +
(two terms smaller by `(17·40/9)^{2000}`)`; reduce to (a) the dominant 2×2 minor ≠ 0 and (b) a
strict-dominance envelope.  Both need the LEADING ASYMPTOTICS of `I₁, I₂` (saddle-point / exact
leading term) — the determinant is exponentially near-degenerate, so coarse bounds will not do.
This is a multi-lap analytic-NT obligation, not a citation.

## Bookkeeping
- `scripts/AxiomAudit.lean`: added `rhinLite_forms_full`, `rhinLiteFD_eq`, `rhinLite_row_relations`,
  `rhinLite_formMatrix_det_cast`, `rhinLite_integralMatrix_det_ne_zero`.  Ledgers: the first four are
  trust-base clean (`propext/Classical.choice/Quot.sound` + the pre-existing `boundProduct`
  native_decide anchor); the det nodes + `rhinLiteLIMeasure` carry `sorryAx` (the one disclosed
  hole).  No Rhin axiom in this subtree.
- `experiments/rhin_lite_det_check.py` (+ `_exact`, `_ratio_exact`): the exact-integer probes.
- Build note (unchanged): warm `lake build` in background before committing; single-module
  RhinLiteApprox rebuild is slow (~200s).
- Do NOT rebuild/weaken the proved apparatus; `rhinLite_forms_bounded_K1` is now unused but retained.
