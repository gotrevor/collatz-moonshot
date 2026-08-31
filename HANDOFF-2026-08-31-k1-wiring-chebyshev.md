# HANDOFF 2026-08-31 — K=1 forms wired + Chebyshev denominator bounds PROVED

- **Branch:** `main`  **Tree:** clean, not pushed.
- `lake build` green (8764 jobs).  `bash scripts/check-proof-debt.sh` = **one** disclosed sorry
  repo-wide: `RhinLiteApprox.lean` (`rhinLiteLIMeasure`).

## Arc of this session (2 green commits after `5322ee9`)

1. **K=1 log forms wired** (`RhinLiteApprox.lean`): `rhinLiteEven_two_log_forms_K1` and
   `rhinLite_forms_bounded_K1` — instantiate `lcm_cleared_log_form_K1` at `P = rhinLiteEvenPolynomialZ t`
   on endpoints `(2,3)`/`(3,4)`, feeding the proved `rhinLiteEvenPolynomialZ_content`.  Smaller
   `D_N = lcmUpto N` (no `12^N`), `B = lcmUpto N·centralCoeff`, `lcmUpto N·17^N ≤ B ≤ lcmUpto N·18^N`,
   `0 < Lᵢ ≤ lcmUpto N·(9/40)^N`.  **The remainder now decays** (`K=1 < τ`), fixing the vacuity that
   `overcleared_remainder_ge_one` diagnosed for the old `12^N` forms.

2. **Chebyshev denominator bounds PROVED** (the finite-exponent `κ` prerequisite):
   - `lcmUpto_log_le_chebyshev`: `log(lcmUpto N) ≤ log4·N + 2√N·log N` — mathlib `Chebyshev.psi_le`
     transported through `Chebyshev.psi_eq_log_lcmUpto`.
   - `lcmUpto_le_pow_eventually`: `∃N₀, ∀N≥N₀, lcmUpto N ≤ (22/5)^N`.  Base `4.4 ∈ (4, 40/9)`, so
     `E_N = lcmUpto N·(9/40)^N ≤ (99/100)^N → 0`.  Proof pulls back `√N·log N = o(N)`
     (`isLittleO_log_rpow_atTop` at `r=1/2`) to a ℕ threshold.  Added
     `import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`.

Both ledgers trust-base-only (added to `scripts/AxiomAudit.lean`).

## State of the crux — `rhinLiteLIMeasure` (the only open sorry)

The mechanism (`logForm_conditional_lower`) is now fed forms with a genuinely decaying `E_N`, and the
denominator asymptotic is proved.  **The single remaining hard node is the non-vanishing determinant.**

## Next lap — hardest-first

1. **Non-vanishing determinant** (THE crux blocker): for `(p,q,r) ≠ 0`, the 3×3 determinant of three
   consecutive form-triples `(B_t, A₁_t, A₂_t)` is a nonzero integer ⇒ `n = p·B − q·A₁ − r·A₂ ≠ 0`
   for ≥1 of three consecutive `t`.  Decompose in `src/` into (a) det is a nonzero integer (Wronskian /
   Padé non-degeneracy of the three approximation triples), (b) "not all three `n` vanish".
   This is the genuine analytic-NT obligation — a multi-lap target, narrow it.
2. **Height→index selection** using `lcmUpto_le_pow_eventually` as the monotone majorant `E_N ≤ (99/100)^N`
   (raw `E_N` is non-monotone): least `t` with `(|q|+|r|)·(99/100)^N ≤ 1/2`, `N ~ log H`.
3. **Assembly**: `|Λ| ≥ 1/(2·lcmUpto N·18^N) ≥ 1/(2·(22/5·18)^N) = c·H^{−κ}`, `κ` finite (crude).

See `PENDING_WORK.md` "★ K=1 WIRING + CHEBYSHEV BOUNDS DONE".

## Bookkeeping

- `scripts/AxiomAudit.lean`: added the four new theorems.
- `scripts/check-proof-debt.sh`: unchanged (still pins the single `RhinLiteApprox` sorry).
- The proved apparatus (content, clearing, mechanism, `sep_two_three`, Chebyshev bounds) must not be
  rebuilt or weakened.
