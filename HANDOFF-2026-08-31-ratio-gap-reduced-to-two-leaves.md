# HANDOFF 2026-08-31 — ratio-gap REDUCED to two one-sided per-interval leaves

- **Branch:** `main`  **Tree:** clean, not pushed.
- `lake build` green (8764 jobs).  `bash scripts/check-proof-debt.sh` = **2** disclosed sorries
  repo-wide, both `RhinLiteApprox.lean` (`:1431` `rhinLiteI₂_peak_upper`, `:1443`
  `rhinLiteI₁_concentration_lower`).

## What this lap did

Attacked the sole remaining crux sorry `rhinLite_ratio_gap` (`2·I₁(t)I₂(t+1) ≤ I₁(t+1)I₂(t)`).
Followed the prior handoff's attack plan exactly:

1. **PROVED the arithmetic reduction** `rhinLite_ratio_gap_of_step_bounds` (trust-base clean):
   from `q₁ ≤ κ·q₀` and `2κ·p₀ ≤ p₁` (same `κ`, `p₀,q₀ ≥ 0`), the gap `2·p₀q₁ ≤ p₁q₀` follows by
   two monotone multiplications (`nlinarith` on the two products).  No cancellation, no analysis.
2. **Fixed the shared constant** `rhinLiteKappa = (2209/10000)^{2·rhinLiteScale}` (`= 0.2209^2000`).
   Verified (via `experiments/rhin_lite_laplace.py` grid-scan, authoritative — the file's Newton
   seeds hit *local* not global peaks; the docstring's "two equal maxima" is STALE) it sits in the
   narrow valid window `[exp(m₂), exp(m₁)/2] = [0.220314^{2000}, 0.221454^{2000}]`:
   `m₁ = max_{[2,3]}ψ = −3014.514` at `x≈2.2232`, `m₂ = max_{[3,4]}ψ = −3025.534` at `x≈3.6524`,
   gap `+11.02`.  Upper needs base `≥0.220314`; lower (`2κ ≤ exp(m₁)`) needs base `≤0.221454`;
   `0.2209` clears both, giving `exp(4.9)≈134×` room on the concentration leaf.
3. **Rewrote `rhinLite_ratio_gap`** as a 4-line term proof feeding the two leaves through the glue.
   `rhinLite_ratio_gap` now carries only `sorryAx` (via the leaves) + the pre-existing bracket
   `native_decide` anchors (through `rhinLiteI₁_pos`/`rhinLiteI₂_pos`).  NO Rhin axiom.

Net: the determinant crux now rests on **two** disclosed sorries instead of one — this is the
decomposition, not a regression.  Everything above them (`det_dominance_of_step_bounds`,
`rhinLite_det_dominance`, `rhinLite_integralMatrix_det_ne_zero`, `rhinLite_formMatrix_det_ne_zero`)
is unchanged and still assembled.

## The two remaining leaves (RhinLiteApprox.lean)

- **`rhinLiteI₂_peak_upper (t)` : `I₂(t+1) ≤ κ·I₂(t)`** — the EASIER, mechanical one.  A POINTWISE
  `[3,4]` step bound `φ(x)² ≤ (2209/10000)^{2·scale}`, tighter than the global `(9/40)^{2·scale}`
  (the `[3,4]` peak `exp(m₂)` is `exp(31)` below the global envelope).  Mirror the decay proof
  `rhinLiteI₂_step_decay16` but replace the global `rhinLiteKernelAbs_div_pow_le_on_Icc` with a
  `[3,4]`-restricted factor-bound from the `RhinLiteInterval` machinery (the `rhinLiteFactorBound`
  table already has per-bracket rounded factor products; the `[3,4]` brackets are rows for
  `rhinLiteRootLeft ≥ 3`).  Need: a lemma `φ(x) ≤ (2209/10000)^{scale}` for `x ∈ [3,4]`, then the
  same `rhinLiteEven_logForm_step_le`-style pointwise integrand argument.  **NEXT LAP: do this one
  first** — it is compiler-grounded and likely closes fully.

- **`rhinLiteI₁_concentration_lower (t)` : `2κ·I₁(t) ≤ I₁(t+1)`** — the genuine Laplace HEART, the
  multi-lap crux.  NOT pointwise (`φ` vanishes at `2` and `3`).  Route in the docstring / PENDING_WORK:
  fix a rational sub-window `[a,b] ⊂ [2,3]` about `x₁*≈2.223` where `φ² ≥ 2κ`; then
  `I₁(t+1) = ∫₂³ φ²·φ^{2t}/x ≥ 2κ·∫_{[a,b]} φ^{2t}/x`, and a tail comparison
  `∫_{[2,3]∖[a,b]} φ^{2t}/x ≤ ∫_{[a,b]} φ^{2t}/x` yields `∫_{[a,b]} φ^{2t}/x ≥ ½·I₁(t)`.  The tail
  comparison is where the concentration lives (map the tail into the window by monotonicity of
  `φ^{2t}` toward the peak).  ⚠ Do NOT chase a global pointwise lower bound (refuted — endpoints).
  ⚠ Do NOT reintroduce single-rate absolute envelopes (recorded FALSE in PENDING_WORK).

## Bookkeeping
- `scripts/AxiomAudit.lean`: added `rhinLiteKappa_pos`, `rhinLite_ratio_gap_of_step_bounds`
  (trust-base clean), `rhinLiteI₂_peak_upper`, `rhinLiteI₁_concentration_lower` (both `sorryAx`).
  `rhinLite_ratio_gap` = `sorryAx` + bracket native_decide anchors only; NO Rhin axiom in subtree.
- `scripts/check-proof-debt.sh`: unchanged gate; now pins exactly the two leaves.
- `PENDING_WORK.md` ★ DOMINANCE NODE sub-node 4 + `STATUS.md` checkpoint updated.
- Do NOT rebuild/weaken: `rhinLite_ratio_gap_of_step_bounds`, `rhinLiteKappa`, `rhinLite_ratio_gap`,
  the three proved per-step leaves, `det_dominance_of_step_bounds`.
- Build note: single-module `lake build CollatzMoonshot.FrontA.RhinLiteApprox` ≈ 30s warm here.
