# HANDOFF 2026-08-31 — sink `sep_two_three` CLOSED (proved modulo cited Rhin 1987 axiom)

- **Branch:** `main`  **Tree:** clean after commit `3da2219` (not pushed).
- `lake build` green (8764 jobs). `bash scripts/check-proof-debt.sh` = **one** disclosed sorry:
  `RhinLiteApprox.lean:380` (`rhinLiteLIMeasure`). PowSeparation.lean is now sorry-free.

## What landed this lap (the crux advance)

Executed DIRECTION/HANDOFF priority 1: **discharged the sink `sep_two_three`** (formerly the
disclosed sorry at `PowSeparation.lean:40`) via option (ii) — a threshold-parametric reduction.

New in `FrontA/PowSeparation.lean` (all sorry-free):
- `sep_of_linear_form_poly_threshold` — the parametric-`K` variant of `sep_of_linear_form_poly`
  (crossover threshold `K` is now a free parameter; residual `6 ≤ k < K` handled by supplied `hfin`).
- `crossover_exp_450` — `3^14·k^14 ≤ exp((k/3)·log2)` for `k ≥ 450`. Base `1350^14 ≤ 2^150`
  (`native_decide`); inductive step `(1+1/n)^14 ≤ exp(14/n) ≤ exp((1/3)log2) = 2^(1/3)` for `n ≥ 61`
  (uses `Real.log_two_gt_d9`). The true crossover is `k ≈ 435`; `450` is a clean `/3` threshold past it.
- `sep_two_three_finite_check_450` / `sep_two_three_small_450` — `native_decide` table over
  near-critical `6 ≤ k < 450`, `m < 713`.
- `log23_effective_measure_concrete` (κ=14, c=1/3^14) — **moved here from RhinLiteApprox** (which now
  imports nothing new; PowSeparation imports `Assumed.Rhin1987`). `log23_effective_measure` (existential
  audit surface) now just repackages it.
- `sep_two_three` — instantiates `sep_of_linear_form_poly_threshold (1/3^14) 14 450` with the three
  discharged hypotheses. `bd_reduction` relocated to follow it (its only in-file consumer).

`#print axioms CollatzMoonshot.FrontA.sep_two_three`:
`[propext, Classical.choice, Quot.sound, rhin_1987_log_two_three_measure,
 crossover_exp_450._native…, sep_two_three_finite_check_450._native…, sep_two_three_small_450._native…]`
— trust base + the ONE cited math axiom (Rhin 1987) + 3 `native_decide` artifacts (lane-2 allowed).
The whole two-block exclusion `le_two_blocks_not_acyclicParadoxical` inherits the same clean ledger.

## State of the crux(es)

- **`sep_two_three` — DONE.** The sink node's β=1/3 separation is machine-checked modulo one cited
  axiom. No further work needed unless the axiom is retired (below).
- **`rhinLiteLIMeasure`** (`RhinLiteApprox.lean:380`, the sole remaining `src/` sorry): its purpose is
  now to **retire** `rhin_1987_log_two_three_measure`, not to close `sep_two_three`. TRUE (Rhin), but
  the `12^N`-cleared forms cannot reach it (scaling bug: `K ≈ 3.49 > τ ≈ 1.49`, witness
  `overcleared_remainder_ge_one`). The elementary apparatus (size bridge, elimination, conditional
  lower bound, data packaging) is all proved; only the **K=1 structural clearing** + non-vanishing
  determinant + `lcmUpto` asymptotic remain — a genuine multi-lap ANT expedition.

## Next lap options (priority order)

1. **Retire the axiom** — the K=1 structural clearing for `rhinLiteLIMeasure` (HANDOFF priority 2):
   prove `12^{N−j} ∣ coeff_j(H_N)` (i.e. `H_N ∈ (12,x)^N ℤ[x]`; content balances already numeric in
   `RhinLite.lean`), redo `lcm_cleared_log_form` with `D_N = lcmUpto N` (so `K = 1 < τ`), then the
   non-vanishing determinant + `lcmUpto ≤ 4^N`. Decompose into named disclosed sorries in
   `RhinLiteApprox.lean` (raising the src count there is progress). See
   `FRONT-A-RHIN-LITE-SCALING-2026-08-31.md`, `PENDING_WORK.md`.
2. **Front B / other headline fronts** — `sep_two_three` no longer blocks Front A's two-block
   exclusion; revisit `FRONT-B-ROUTES.md` and `FRONT-A-ROUTES.md` for the next weakest node.

## Bookkeeping

- `scripts/AxiomAudit.lean`: added `log23_effective_measure_concrete`, `crossover_exp_450`,
  `sep_two_three_small_450`, `sep_of_linear_form_poly_threshold`, `sep_two_three`, `bd_reduction`.
- `scripts/check-proof-debt.sh`: gate now expects the single sorry in `RhinLiteApprox.lean` only
  (PowSeparation.lean sorry-free); removed the `pow_hits == 1` requirement.
- Docs updated: `README`, `STATUS`, `PENDING_WORK`. `DIRECTION.md` pointer unchanged (still accurate;
  the "Next live theorem" there is now `rhinLiteLIMeasure` for axiom retirement).
