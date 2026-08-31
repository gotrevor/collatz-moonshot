# HANDOFF 2026-08-31 — dominance node DECOMPOSED into 4 per-step sub-nodes (glue PROVED)

- **Branch:** `main`  **Tree:** clean, not pushed.
- `lake build` green (8764 jobs).  `bash scripts/check-proof-debt.sh` = **4** disclosed sorries,
  all in `RhinLiteApprox.lean`, all the named per-step sub-nodes below.

## What this lap did

Took the sole crux `rhinLite_det_dominance` (previously one opaque analytic `sorry`) and reduced it
to **four clean, disclosed per-step sub-nodes**, proving the entire pure-arithmetic assembly that
combines them.  Net: crux count 1 → 4, but each new hole is a concrete, O(1)-margin, well-understood
analytic fact instead of an opaque monolith.  All glue is machine-checked and trust-base clean.

### PROVED (no sorry, trust-base clean)
`det_dominance_of_step_bounds` — abstract lemma over the nine determinant entries `c₀,c₁,c₂`
(central column), `p₀,p₁,p₂ = I₁`, `q₀,q₁,q₂ = I₂`.  Hypotheses (all clean per-step facts):
- ratio-gap `2·(p₀q₁) ≤ p₁q₀`,
- per-step decay `16 p₂ ≤ p₁`, `16 q₂ ≤ q₁`, `q₂ ≤ q₁`, `q₁ ≤ q₀`,
- central per-step growth `16 c₀ ≤ c₂`, `16 c₁ ≤ c₂`.

Conclusion `c₂(p₁q₀ − p₀q₁) > |c₀(p₁q₂−q₁p₂)| + |c₁(p₀q₂−q₀p₂)|`.  Proof: each RHS monomial
`≤ (c₂p₁q₀)/16` ⇒ sum `≤ (c₂p₁q₀)/4 < (c₂p₁q₀)/2 ≤ LHS` (the last from the ratio-gap).  No
cancellation.  `rhinLite_det_dominance` is then this lemma fed by the sub-nodes, with the goal's
`|c₂·M(0,1)|` rewritten to `c₂(p₁q₀−p₀q₁)` via `abs_of_nonpos` (sign of `M(0,1)` from the gap).

### The 4 disclosed sub-nodes (all TRUE with huge room)
1. `rhinLiteI₁_step_decay16` : `16·I₁(t+1) ≤ I₁(t)`  (true per-step rate `exp(−3014.5)`).
2. `rhinLiteI₂_step_decay16` : `16·I₂(t+1) ≤ I₂(t)`  (true rate `exp(−3025.5)`).
3. `rhinLiteCentral_step_growth16` : `16·c(t) ≤ c(t+1)`  (true `≈ 17^2000`).
4. `rhinLite_ratio_gap` : `2·I₁(t)I₂(t+1) ≤ I₁(t+1)I₂(t)`  (the `μ₁>M₂` separation, gap `exp 11`).

## KEY CORRECTION over the prior handoff (`det-dominance.md`)

The prior route ("independent two-sided *absolute* exp envelopes on `I₁,I₂` + `μ₁>M₂` ⟹ dominance
by arithmetic") does **not** close the `|M(0,1)|` LOWER bound: `I₁(t₀)I₂(t₀+1) − I₂(t₀)I₁(t₀+1)`
has both products of near-equal rate, so an absolute envelope loses the correlation and
`ℓ₂ℓ₁ − u₁u₂ < 0` for large `t₀`.  Likewise the loose central band `17^N ≤ c ≤ 18^N` CANNOT compare
consecutive `c`'s (slack `(18/17)^N` compounds).  **Fix: per-step RATIO (multiplicative) bounds** —
sub-nodes 1–4 are exactly these, and with them the assembly is subtraction-free and clean.  This is
the structural insight of the lap; the abstract lemma is stated to consume ratio bounds only.

## NEXT ATTACK

Discharge the four sub-nodes (each an O(1)-margin fact; no `√N` Laplace precision needed):
- (1)(2) per-step decay ≥16: uniform envelope for `H_N/x^{N+1}` on each interval across `N→N+2000`
  (lever: `RhinLiteMaximum`/`RhinLiteInterval` bracket machinery; the `x^{-2000}` factor already
  contributes a large decay, plus the peak-value drop).
- (3) central per-step ratio ≥16: `c_{N+2000}/c_N` from the explicit coefficient structure of `H_N`.
- (4) ratio-gap: separated Laplace maxima `m₁>m₂` — bound `∫₂³` below / `∫₃⁴` above by peak
  contributions (`RhinLiteCritical`/`RhinLiteInterval`).  This is the analytic heart.

Good first target: (4), since it is the single fact that makes the determinant nonzero (the sign +
magnitude of the dominant minor) and reuses the most existing bracket infrastructure.

## Bookkeeping
- `scripts/AxiomAudit.lean`: added `det_dominance_of_step_bounds` (trust-base clean) + the four
  sub-nodes (each `sorryAx`) + `rhinLite_det_dominance` (carries `sorryAx` via the sub-nodes).  No
  Rhin axiom anywhere in this subtree.
- `scripts/check-proof-debt.sh`: unchanged gate (location-pinned to RhinLiteApprox; count may grow
  under decomposition — now 4).
- `PENDING_WORK.md`: new "★ DOMINANCE NODE — DECOMPOSED" section at top with the correction + attack.
- Do NOT rebuild/weaken the proved apparatus (`det_cast`, `cofactor`, positivity, assembly).
- Build note: single-module `lake build CollatzMoonshot.FrontA.RhinLiteApprox` ≈ 200s; warm before
  committing.
