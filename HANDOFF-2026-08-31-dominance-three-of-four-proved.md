# HANDOFF 2026-08-31 — dominance crux: 3 of 4 per-step leaves PROVED; one node remains

- **Branch:** `main`  **HEAD:** `3bac663`  **Tree:** clean, not pushed.
- `lake build` green (8764 jobs).  `bash scripts/check-proof-debt.sh` = **1** disclosed sorry
  repo-wide: `RhinLiteApprox.lean:1409` (`rhinLite_ratio_gap`).

## Arc of this session

The determinant crux `rhinLite_formMatrix_det_ne_zero` (retiring the cited Rhin measure axiom) was
reduced last lap to the single dominance inequality `rhinLite_det_dominance`.  This session:

1. **PROVED the pure-arithmetic assembly** `det_dominance_of_step_bounds` (trust-base clean) and
   decomposed `rhinLite_det_dominance` into FOUR per-step sub-nodes (commit `127bfba`).
2. **Caught + reverted an UNSOUND sub-approach** (commits `82af17c`, `c870c8a`, reverted by
   `278f170`, `1e4590e`): "single-rate absolute envelopes" `c·rᵗ ≤ Iᵢ(t) ≤ C·rᵗ` are FALSE — Laplace
   gives `Iᵢ(t) ~ M^{2t}/√t`, so no constant lower envelope exists at the true rate.  The honest form
   is the per-step RATIO facts.  (Recorded in `PENDING_WORK.md`; do NOT reintroduce.)
3. **PROVED both integral decays** `rhinLiteI₁_step_decay16`, `rhinLiteI₂_step_decay16` (commit
   `132bb53`, trust-base clean).  KEY: the normalized integrand is a PURE POWER
   `rhinLiteEvenNormalized t x = (kernelAbs x/x¹⁰⁰⁰)^{2t}` (`rhinLiteEvenNormalized_eq`), so
   `normalized(t+1)=φ²·normalized(t)` with `φ ≤ (9/40)¹⁰⁰⁰` (global bound), a fixed per-step drop
   `(9/40)²⁰⁰⁰ ≤ 1/16`.  New: `rhinLiteKernelAbs_nonneg`, `rhinLiteEven_logForm_step_le`,
   `rhinLite_stepFactor_le_one_sixteenth`.
4. **PROVED central growth** `rhinLiteCentral_step_growth16` (commit `3bac663`, trust-base clean —
   only the pre-existing band `native_decide` anchor).  By CONVOLUTION POSITIVITY: `rhinLitePositive`
   has nonneg coeffs + power law `P(a+b)=P(a)·P(b)`, so `c(t+1) ≥ c(t)·c(1) ≥ 16·c(t)`.  New:
   `rhinLitePositive_add`, `rhinLitePositive_coeffNonneg`, `rhinLiteCentral_coeff_link`.

Net: the entire determinant crux now rests on **one** disclosed sorry.

## THE sole remaining obligation

`rhinLite_ratio_gap (t)` : `2·I₁(t)I₂(t+1) ≤ I₁(t+1)I₂(t)` — the `μ₁ > M₂` separation (`I₁` decays
strictly slower than `I₂`; true gap `exp 11 ≈ 6·10⁴ ≫ 2`).  This is the analytic HEART: the separated
maxima of `ψ` on `[2,3]` vs `[3,4]`.

**Why it is genuinely harder than the decays (do not chase the global bound):** the pure-power trick
only gives an UPPER per-step bound `Iᵢ(t+1) ≤ (9/40)²⁰⁰⁰·Iᵢ(t)` for BOTH intervals.  The gap needs a
LOWER bound on `I₁(t+1)/I₁(t)` exceeding twice the `I₂`-upper — i.e. the `[2,3]`-peak must beat the
`[3,4]`-peak.  Since `φ` vanishes at the interval endpoints, no pointwise lower bound works; the mass
of `φ^{2t}` must CONCENTRATE near the higher peak (a Laplace lower bound).

**Concrete attack (next lap):**
- Reduce (proved-arithmetic helper, ~10 lines): gap ⟸ `I₂(t+1) ≤ κ·I₂(t)` (per-interval `[3,4]`
  peak upper `κ = M₂²`) AND `I₁(t+1) ≥ 2κ·I₁(t)` (the concentration lower bound).
- The concentration lower bound: pick a fixed sub-window `[a,b] ⊂ [2,3]` around `x₁* ≈ 2.223` where
  `φ ≥ φ_lo` with `φ_lo² ≥ 2M₂²` (huge margin: `M₁/M₂ ≈ 245`); then
  `I₁(t+1) = ∫₂³ φ²φ^{2t}/x ≥ 2M₂² ∫_{[a,b]} φ^{2t}/x`, and bound the tail
  `∫_{[2,3]∖[a,b]} φ^{2t}/x ≤ ∫_{[a,b]}` (Laplace tail: `φ` on the tail ≤ `φ` on a matching part of
  the window) to get `∫_{[a,b]} ≥ ½ I₁(t)`.  Requires per-interval peak values (rational enclosures)
  from the `RhinLiteCritical`/`RhinLiteInterval` bracket machinery localized to `[2,3]` and `[3,4]`.

## Bookkeeping
- `scripts/AxiomAudit.lean`: all new decls added; the three proved leaves + helpers are trust-base
  clean (decays: `propext/choice/Quot.sound`; central: + the band `native_decide` anchor).
  `rhinLite_ratio_gap` + `rhinLite_det_dominance` + the two det theorems + `rhinLiteLIMeasure` carry
  `sorryAx` (the one disclosed hole).  No Rhin axiom in this subtree.
- `scripts/check-proof-debt.sh`: unchanged gate (RhinLiteApprox only); now pins the single sorry.
- `PENDING_WORK.md`: top section "★ DOMINANCE NODE" updated (3 leaves PROVED, ratio_gap attack plan,
  the reverted-envelope refutation).
- Do NOT rebuild/weaken: `det_dominance_of_step_bounds`, `rhinLiteEven_logForm_step_le`,
  `rhinLiteCentral_step_growth16` and their helpers.
- Build note: single-module `lake build CollatzMoonshot.FrontA.RhinLiteApprox` ≈ 200s; warm before
  committing.
