# HANDOFF 2026-08-31 — determinant crux collapsed to ONE numerical node

- **Branch:** `main`  **HEAD:** `42dce05`  **Tree:** clean, not pushed.
- `lake build` green (8764 jobs).  `bash scripts/check-proof-debt.sh` = **1** disclosed sorry
  repo-wide: `RhinLiteApprox.lean` `rhinLiteI₁_ratio_base`.

## Arc of this session (6 green commits)

Started with the dominance crux resting on the single sorry `rhinLite_ratio_gap`
(`2·I₁(t)I₂(t+1) ≤ I₁(t+1)I₂(t)`).  Drove it to a single numerical node:

1. **`63a0ee0`** — `rhinLite_ratio_gap` REDUCED to two one-sided per-interval leaves via the
   arithmetic glue `rhinLite_ratio_gap_of_step_bounds` (PROVED) and shared constant
   `rhinLiteKappa = (2209/10000)^{2·scale}` (verified in the valid window `[exp(m₂), exp(m₁)/2]`).
2. **`8e38642` + `2338345`** — `rhinLiteI₂_peak_upper` (`I₂(t+1) ≤ κ·I₂(t)`) FULLY PROVED.  Built
   the μ-parametric step lemma `rhinLiteEven_logForm_step_le_of_bound`, then the tight `[3,4]`
   kernel bound `rhinLiteKernelAbs_div_pow_le_on_Icc34` (a `[3,4]`-restricted compact-max bridge in
   `RhinLiteMaximum.lean` + a tight bracket certificate `rhinLite_boundProduct_certificate_tight` in
   `RhinLiteInterval.lean` — the EXISTING rounded factor table already clears the `exp(18)`-tighter
   target on the three `[3,4]` brackets, no recomputation).
3. **`73ed50c` → `ac3b1d3`** — the concentration lower bound `rhinLiteI₁_concentration_lower`
   (`2κ·I₁(t) ≤ I₁(t+1)`).  ⚠ **CAUGHT AN UNSOUNDNESS:** my first decomposition rested on
   `rhinLiteWindow_mass_half` (`I₁(t) ≤ 2∫_window`), which is FALSE at small `t` (at `t=0` the mass is
   uniform: `I₁(0)=0.405` vs `2∫_window=0.013`).  Replaced with a SOUND log-convexity induction:
   the step ratio `I₁(t+1)/I₁(t)` is nondecreasing (moment log-convexity), so it stays `≥` its base
   value `I₁(1)/I₁(0) ≥ 2κ`.  Induction PROVED (`nlinarith`).
4. **`42dce05`** — the log-convexity node `rhinLiteI₁_logConvex` (`I₁(t+1)² ≤ I₁(t)·I₁(t+2)`)
   PROVED trust-base clean, via a general reusable interval Cauchy–Schwarz
   `interval_sq_integral_cauchySchwarz` (also PROVED, trust-base clean; `L²`-Hölder
   `integral_mul_le_Lp_mul_Lq_of_nonneg`, `MemLp` from the extreme-value bound on `[a,b]`).  Applied
   with `u=√(φ^{2t}/x)`, `v=√(φ^{2t+4}/x)`, `u·v = φ^{2t+2}/x`.

Net: dominance → ratio_gap → concentration_lower is fully assembled and proved; the entire crux
(which retires the cited Rhin measure axiom for the determinant) now rests on ONE numerical node.

## THE sole remaining obligation

`rhinLiteI₁_ratio_base` : `2 * rhinLiteKappa * rhinLiteI₁ 0 ≤ rhinLiteI₁ 1`.
- `I₁(0) = ∫₂³ dx/x = log(3/2) ≈ 0.4055` (exact, elementary).
- `I₁(1) = ∫₂³ φ²/x` where `φ² = (kernelAbs/x^{scale})²`.  Numerically `I₁(1) ≈ exp(−3020.0)`,
  `2κ·I₁(0) ≈ exp(−3020.3)` — margin only `exp(0.29) ≈ 1.34×`, TIGHT.
- **Attack:** lower-bound `I₁(1) = ∫₂³ φ²/x ≥ ∫_W φ²/x` for a sub-window `W ⊂ [2,3]`, then
  `∫_W φ²/x ≥ (min_W φ²)·(∫_W dx/x)`.  Need `(min_W φ²)·(log of W ratio) ≥ 2κ·log(3/2)`.  Because
  this is a SINGLE integral (only `t=1`, no `∀t`), the window may be chosen freely to balance the
  min-height vs the `1/x`-mass — unlike the refuted `∀t` window approach.  The min-height `min_W φ²`
  is a per-interval LOWER kernel bound; ⚠ a single-window independent-factor-min certificate is
  `~18` digits too loose (the factor `f₂=x−2` has `W₂=551·Δln≈35`), so use either (a) a concavity
  argument `ψ''<0` reducing `min_W ψ` to two endpoint evaluations, or (b) ~30–50 sub-brackets.
  Both recorded in `PENDING_WORK.md` ★ DOMINANCE NODE.
- Handy: `rhinLiteEven_logForm_step_ge_of_bound` (PROVED, trust-base clean) already converts a
  pointwise `μ ≤ φ²` on `[a,b]` into `μ·∫_[a,b] φ^{2t}/x ≤ ∫_[a,b] φ^{2t+2}/x`; with `t=0` that is
  exactly `μ·(∫_W dx/x) ≤ ∫_W φ²/x`, so the base case reduces to `min_W φ² ≥ μ` plus
  `∫_W dx/x ≥ 2κ·log(3/2)/μ` (both elementary once the window is fixed).

## Bookkeeping
- `scripts/AxiomAudit.lean`: all new decls added.  Trust-base clean (`propext/choice/Quot.sound`):
  `rhinLite_ratio_gap_of_step_bounds`, `rhinLiteKappa_pos`, `rhinLiteEven_logForm_step_le_of_bound`,
  `rhinLiteEven_logForm_step_ge_of_bound`, `interval_sq_integral_cauchySchwarz`,
  `rhinLiteI₁_logConvex`.  `native_decide`-carrying (bracket certs, no math axiom):
  `rhinLite_boundProduct_certificate_tight`, `rhinLiteKernelAbs_div_pow_le_tight`,
  `rhinLiteRootLeft_ge_three`, `rhinLiteKernelAbs_div_pow_le_on_Icc34`, `rhinLiteI₂_peak_upper`.
  `sorryAx` only via the one hole: `rhinLiteI₁_ratio_base`, `rhinLiteI₁_concentration_lower`,
  `rhinLite_ratio_gap`, `rhinLite_det_dominance`, the two det theorems, `rhinLiteLIMeasure`.  NO
  Rhin axiom anywhere in this subtree.
- `scripts/check-proof-debt.sh`: unchanged gate; now pins the single sorry.
- `PENDING_WORK.md` ★ DOMINANCE NODE + `STATUS.md` updated (single-node status; the two refuted
  sub-approaches recorded: unsound `window_mass_half`, and the too-loose single-window factor-min).
- Do NOT rebuild/weaken any of the PROVED lemmas above, nor `det_dominance_of_step_bounds`,
  `rhinLiteCentral_step_growth16`, the two decays.
- Build note: single-module `lake build CollatzMoonshot.FrontA.RhinLiteApprox` ≈ 17s warm.
