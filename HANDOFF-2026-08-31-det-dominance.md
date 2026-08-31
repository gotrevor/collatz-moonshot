# HANDOFF 2026-08-31 — integral-det node reduced to ONE clean-dominance inequality

- **Branch:** `main`  **HEAD:** `9c489d9`  **Tree:** clean, not pushed.
- `lake build` green (8764 jobs).  `bash scripts/check-proof-debt.sh` = **one** disclosed sorry
  repo-wide: `RhinLiteApprox.lean:1205` (`rhinLite_det_dominance`).

## Arc of this session (5 green commits, `1f57e56 → 9c489d9`)

Drove the sole crux `rhinLite_formMatrix_det_ne_zero` (the node retiring the cited Rhin measure
axiom) from an opaque unevaluable `Classical.choose` integer determinant down to a SINGLE clean
analytic inequality, all glue machine-checked.  Chain (all in `FrontA/RhinLiteApprox.lean`):

1. **Numeric sanity-check** (`experiments/rhin_lite_det_check.py`, exact bigints): the determinant
   is NONZERO for our `N=2000t` spacing-2000 subsequence (`t₀=1`: `log₁₀|det|≈3570`).  NOT refuted.
2. **Retired `Classical.choose` opacity:** `rhinLite_forms_full` / `rhinLiteFD_eq` /
   `rhinLite_row_relations` expose `B = lcmUpto N·centralCoeff`, `lcmUpto N·∫ᵢ = Aᵢ + B·log(·)`.
3. **Column-reduction PROVED:** `rhinLite_formMatrix_det_cast` — `(det:ℝ) = D_{N₀}D_{N₁}D_{N₂}·det(c_N,I₁,I₂)`,
   so `rhinLite_formMatrix_det_ne_zero` is PROVED from the real node `rhinLite_integralMatrix_det_ne_zero`.
4. **Cofactor + positivity PROVED:** `rhinLite_integralMatrix_det_cofactor`
   (`det = c₀M(1,2) − c₁M(0,2) + c₂M(0,1)`), `rhinLiteCentral_pos/rhinLiteI₁_pos/rhinLiteI₂_pos`.
5. **BREAKTHROUGH (corrected a wrong assessment):** `experiments/rhin_lite_laplace.py` (float
   grid-scan of the per-`t` profile `ψ`) shows `I₁,I₂` have **separated** exponential rates —
   `m₁=max_{[2,3]}ψ≈−3014.5 > m₂=max_{[3,4]}ψ≈−3025.5` (gap ≈11), central rate `γ≈5700 ≫ m₁`.  So the
   determinant is **clean single-term dominance**, NOT the "delicate cancellation" I wrongly claimed
   earlier (that assumed both integrals share rate `(9/40)^N`).  Predicted `log₁₀|det|≈3524` matches
   the exact `3570`.
6. **Reduced to ONE analytic sorry:** `rhinLite_integralMatrix_det_ne_zero` is PROVED (reverse
   triangle) from `rhinLite_det_dominance` = `|c(t₀+2)·M(0,1)| > |c(t₀)·M(1,2)| + |c(t₀+1)·M(0,2)|`.

## The SOLE remaining obligation

`rhinLite_det_dominance (t₀)` — the single cofactor term dominates the other two in absolute value.
It encapsulates ALL remaining analytic content.  **Route (no Laplace √N needed — margins `exp(8681 t)`):**
- exp two-sided bounds `I₁(t) ∈ [·exp(t μ₁), ·exp(t M₁)]` on `[2,3]` (rate `m₁`), same for `I₂` on
  `[3,4]` (rate `m₂`), with enclosing RATIONAL rates;
- proved central band `17^N ≤ c_N ≤ 18^N` (`rhinLiteEvenPolynomialZ_centralCoeff_bounds`);
- rate separations `μ₁ > M₂` (gap 11) and `γ_lo − M₁ > 0` (≈8681) ⟹ dominance by arithmetic.

**Next-lap sub-nodes to name in `src/`:**
(a) upper bounds `max_{[2,3]}ψ ≤ m₁+ε`, `max_{[3,4]}ψ ≤ m₂+ε` and the gap — lever is the
`RhinLiteMaximum`/`RhinLiteCritical`/`RhinLiteInterval` critical-bracket machinery (already proves a
`(9/40)^N` envelope; needs the per-interval SEPARATE maxima instead);
(b) exp LOWER bounds on `I₁,I₂` via a fixed sub-window where `ψ ≥ m_i − ε` (continuity + positivity
`rhinLiteEvenIntegral_pos_23/34`);
(c) the arithmetic assembly of `rhinLite_det_dominance` from (a),(b) + the central band — this is
provable NOW as a standalone lemma taking the four exp bounds as hypotheses (good first target).

## Bookkeeping
- `scripts/AxiomAudit.lean`: all new decls added; glue lemmas (forms_full, FD_eq, row_relations,
  det_cast, cofactor, positivity) are trust-base clean; `det_dominance` + the two det theorems +
  `rhinLiteLIMeasure` carry `sorryAx` (the one disclosed hole).  No Rhin axiom in this subtree.
- `scripts/check-proof-debt.sh`: unchanged gate (pins the single RhinLiteApprox sorry).
- `PENDING_WORK.md` "★ BREAKTHROUGH": full route + constants.  Earlier "(a′)/(a) refutation" notes
  are marked SUPERSEDED (their rate assumptions were wrong).
- Experiments: `rhin_lite_det_check.py` (exact det), `rhin_lite_det_modp.py` (mod-p per-t₀ cert,
  refuted for ∀t₀), `rhin_lite_laplace.py` (the rate constants).  No mpmath on box (no egress); float
  suffices for the O(1) Laplace constants.
- Build note: warm `lake build` in background before committing; single-module RhinLiteApprox
  rebuild ~200s.  Do NOT rebuild/weaken the proved apparatus.
