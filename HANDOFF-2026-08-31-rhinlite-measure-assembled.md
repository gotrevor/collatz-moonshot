# HANDOFF 2026-08-31 — rhinLiteLIMeasure ASSEMBLED; crux = one 3×3 determinant

- **Branch:** `main`  **HEAD:** `1f57e56`  **Tree:** clean, not pushed.
- `lake build` green (8764 jobs).  `bash scripts/check-proof-debt.sh` = **one** disclosed sorry
  repo-wide: `RhinLiteApprox.lean:951` (`rhinLite_formMatrix_det_ne_zero`).

## What this session did (8 green commits, `43e816b → 1f57e56`)

Drove the Rhin-lite crux `rhinLiteLIMeasure` (the theorem that retires the cited
`Assumed.rhin_1987_log_two_three_measure` axiom) from a single monolithic `sorry` to a fully
machine-checked transference resting on ONE standard determinant statement.  All in
`CollatzMoonshot/FrontA/RhinLiteApprox.lean`.

PROVED this session (all trust-base clean, in `scripts/AxiomAudit.lean`):
- `rhinLiteEven_two_log_forms_K1`, `rhinLite_forms_bounded_K1` — the K=1 log forms with the smaller
  `D_N = lcmUpto N` (decaying remainder `E_N = lcmUpto N·(9/40)^N`).
- `lcmUpto_log_le_chebyshev`, `lcmUpto_le_pow_eventually`, `lcmUpto_remainder_majorant` — the
  Chebyshev denominator bounds: `E_N ≤ (99/100)^N → 0`, `lcmUpto N·18^N ≤ (396/5)^N`.
- `rhinLite_pointwise_lower` — assembly core: at a good `t`, `|Λ| ≥ 1/(2·B(t))`.
- `rhinLite_selection_envelope` — the log/rpow height→index selection + envelope
  `lcmUpto N·18^N ≤ C·H^κ`, `κ = ⌈log(396/5)/log(100/99)⌉`.
- `rhinLiteLIMeasure` — full transference, `|Λ| ≥ (1/(2C))/H^κ` (PROVED modulo the one node below).
- `rhinLite_n_eq` — `(n(t):ℝ) = B(t)·Λ − q·L₁(t) − r·L₂(t)` (from `elim_identity`).
- `rhinLite_nonvanishing_of_large` — if `Λ ≠ 0` then `n(t) ≠ 0` for all large `t`.
- `rhinLite_nonvanishing_triple` — PROVED from the determinant node via clean linear algebra
  (`Matrix.eq_zero_of_mulVec_eq_zero`): `(M *ᵥ ![p,-q,-r])ᵢ = n(t₀+i)`.

## The SOLE remaining obligation

`rhinLite_formMatrix_det_ne_zero (t₀) : (rhinLiteFormMatrix t₀).det ≠ 0`
— the 3×3 integer matrix of rows `(B, A₁, A₂)` at `t₀, t₀+1, t₀+2` is nonsingular.  This is Rhin's
genuine perfect-system non-degeneracy core.  Everything else (measure, envelope, mechanism,
reformulation, conditional non-vanishing, `sep_two_three`, content, clearing) is machine-checked.

## Next lap — attack `rhinLite_formMatrix_det_ne_zero`

The `B/A₁/A₂` are currently `Classical.choose`-opaque (from `rhinLite_forms_bounded_K1`), so the
determinant cannot be evaluated as-is.  Route:
1. Make `B(t), A₁(t), A₂(t)` EXPLICIT as coefficient sums (they come from `lcm_cleared_log_form_K1`
   / `isInt_finset_sum` in `RhinLiteLogForm.lean`): `B = lcmUpto N · centralCoeff`, and `A₁,A₂` are
   the cleared tail sums.  Prove `rhinLiteB t = lcmUpto (2000t)·H_N.coeff (2000t)` etc.
2. Column-reduce `(B,A₁,A₂) ↦ (B, L₁, L₂)` (unimodular; `L_i = D_N∫`), so `det` = `det(B_i,L_i)`.
3. The Rhin/Wu perfect-system evaluation: `det` is a fixed nonzero integer.  This is the genuine
   multi-lap explicit-construction formalization — narrow it, don't expect a one-lap close.
   ⚠ First VERIFY the determinant is actually nonzero for OUR six-factor `N=2000t` subsequence
   (spacing 2000, not `n,n+1,n+2`) — sanity-check before committing to the proof.

See `PENDING_WORK.md` "★ ... determinant" for the full reduction chain and the two attack routes.

## Bookkeeping
- `scripts/AxiomAudit.lean`: all new theorems added.
- `scripts/check-proof-debt.sh`: unchanged (pins the single `RhinLiteApprox` sorry; location gate).
- Build note: single-module rebuild of `RhinLiteApprox` is slow (~200s single-threaded); the
  pre-commit hook build can exceed a 400s tool timeout — warm `lake build` in background first,
  then commit (the pre-commit replays cache in seconds).
- Do NOT rebuild/weaken the proved apparatus.
