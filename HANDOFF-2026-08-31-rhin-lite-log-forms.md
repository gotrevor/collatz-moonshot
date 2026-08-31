# HANDOFF 2026-08-31 — Rhin-lite objectives 2 & 3 complete

- **Branch:** `main`  **HEAD:** `8137524`  **Tree:** clean (all committed, not pushed).
- `lake build` green (8762 jobs); `bash scripts/check-proof-debt.sh` = exactly the one disclosed
  `CollatzMoonshot/FrontA/PowSeparation.lean:40` sorry.

## What landed this session

Both operator objectives from `FRONT-A-RHIN-LITE-NEXT.md` are complete and sorry-free.

**Objective 2 — even-block lift** (`CollatzMoonshot/FrontA/RhinLiteEven.lean`):
- `rhinLiteEvenPolynomial` at `N = 2000t`; `rhinLiteEvenPolynomial_natDegree` (exact `2N`);
  `coeff_comp_neg_X` + `rhinLiteEvenPolynomial_comp_neg_X` identify it with `rhinLitePositive (2t)`,
  giving `rhinLiteEvenPolynomial_centralCoeff_bounds` (`17^N ≤ B_N ≤ 18^N`).
- `rhinLiteEvenNormalized_eq` (= `(|H|/x^1000)^{2t}`), `_nonneg`, `_le` (`≤ (9/40)^N` on `[2,4]`).
- Interval integrals: `continuousOn_…`, `intervalIntegrable_…`, `rhinLiteEvenIntegral_le`
  (`∫ ≤ length·(9/40)^N`), `_nonneg`, and strict positivity `rhinLiteEvenIntegral_pos_23`/`_34`.

**Objective 3 — integer log forms** (`CollatzMoonshot/FrontA/RhinLiteLogForm.lean`):
- `integral_monomial_div_pow` → `integral_poly_div_pow` → `integral_poly_div_pow_split`
  (log term isolated from the rational tail).
- Clearing arithmetic: `sub_natCast_dvd_lcmUpto`, `endpoint_pow_dvd_twelve_pow`,
  `twelve_pow_mul_zpow_isInt`, `tail_term_cleared`, `isInt_finset_sum`.
- `lcm_cleared_log_form`: for integer `P` of degree in `[N,2N]`, endpoints `ea≤eb ∣ 12`,
  `D_N·∫_{ea}^{eb} P/x^{N+1} = A + B·log(eb/ea)`, `A,B:ℤ`, `B = D_N·P.coeff N`,
  `D_N = lcmUpto N·12^N`.
- **Headline** `rhinLiteEven_two_log_forms`: integer `H_N = rhinLiteEvenPolynomialZ t` (degree `2N`,
  casts to the rational even polynomial, central coeff in `[17^N,18^N]`) instantiated at `(2,3)`
  and `(3,4)` gives `A₁,A₂,B:ℤ` with `D_N·∫_2^3 = A₁ + B·log(3/2)`, `D_N·∫_3^4 = A₂ + B·log(4/3)`,
  the SAME `B`, and `D_N·17^N ≤ B ≤ D_N·18^N`.

All principal theorems are in `scripts/AxiomAudit.lean` with clean ledgers (only
`propext, Classical.choice, Quot.sound` plus the already-allowed `native_decide` interval/root/
coefficient certificates; no `sorryAx` or new math axiom).

## Next steps (toward the sink node `sep_two_three`)

The remainder-integral machinery and the coefficient band are now both in hand. What's left is the
**final simultaneous-approximation criterion**:

1. The two forms `A₁ + B·log(3/2)`, `A₂ + B·log(4/3)` are a nonzero (positivity: objective 2's
   `rhinLiteEvenIntegral_pos_23/_34` show the integrals `> 0`) integer linear combination of
   `1, log(3/2), log(4/3)`.
2. Size: `D_N·∫ ≤ D_N·(9/40)^N` per interval (from `rhinLiteEvenIntegral_le`), while the
   coefficient `B ≥ D_N·17^N`. The decisive arithmetic is `12·(9/40) = 27/10`: check
   `lcmUpto N · 12^N · (9/40)^N = lcmUpto N · (27/10)^N` against `Nat.lcmUpto_le` (`≤ 4^N·e^{o(N)}`)
   — need the product `→ 0` (or a clean bound) to run the standard irrationality/measure argument.
   NOTE: `27/10 = 2.7 > 1`, so the naive `(27/10)^N` does NOT decay — the correct pairing likely
   normalizes differently (the `12^N` clears endpoint denominators but the *decay* is against the
   central coefficient `B ≥ 17^N`, not against `12^N`). Re-derive which quantity is the small
   remainder before coding: it is `Λ_N := ∫ H_N/x^{N+1}` un-cleared, with `|Λ_N| ≤ (9/40)^N` and the
   integer combination `D_N·Λ_N = A + B log`. The working inequality is `lcmUpto N·(9/40)^N·(size of
   B factor)` — reconcile with the Legendre single-log template `legendre_log_two_small`
   (`FrontA/Legendre.lean`) which is the proven analogue for `log 2`.
3. Feed the resulting finite measure through `sep_of_linear_form_poly` / the `PowSeparation.lean`
   interface and extend the finite `native_decide` check that closes small `k`.

Read `FRONT-A-RHIN-LITE.md` (steps 3–4), `PENDING_WORK.md`, and the Legendre single-log
assembly (`legendre_mobius_linear_form`, `legendre_mobius_ne_zero`, `legendre_log_two_small`) as
the structural template for step 2–3.
