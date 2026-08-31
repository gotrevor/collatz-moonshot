# HANDOFF 2026-08-31 — Rhin-lite even-block lift (objective 2, pointwise) complete

## Concrete advance

Landed `CollatzMoonshot/FrontA/RhinLiteEven.lean` (root-imported in `CollatzMoonshot.lean`),
executing objective 2 of `FRONT-A-RHIN-LITE-NEXT.md` up to the pointwise bound:

- `rhinLiteEvenPolynomial t` — the original signed six-factor polynomial at `N = 2000t`.
- `rhinLiteEvenPolynomial_natDegree` — exact degree `2N` (`compute_degree!` + `omega`).
- `coeff_comp_neg_X` (reusable) and `rhinLiteEvenPolynomial_comp_neg_X` — the `(-X)`-substitution
  identifies the even polynomial with `rhinLitePositive (2t)` factor-by-factor (`keyN`/`keyP` even
  power lemmas), so `rhinLiteEvenPolynomial_centralCoeff` shows the central coefficient equals the
  already-certified positive coefficient, and `rhinLiteEvenPolynomial_centralCoeff_bounds` places
  it in `[17^N, 18^N]`.
- `rhinLiteEvenNormalized` = `aeval x (poly) / x^N`; `rhinLiteEvenNormalized_eq` proves it equals
  `(rhinLiteKernelAbs x / x^1000)^{2t}` exactly (`even_base_pow_abs` helper), hence
  `rhinLiteEvenNormalized_nonneg` and `rhinLiteEvenNormalized_le` (`≤ (9/40)^N` on `[2,4]`, by
  raising the base theorem `rhinLiteKernelAbs_div_pow_le_on_Icc` to `2t`).

Four new headline theorems added to `scripts/AxiomAudit.lean`; ledgers are clean (only
`propext, Classical.choice, Quot.sound` plus already-allowed `native_decide` interval/root certs).

## Exact verification

- `lake build` — green, 8761 jobs.
- `bash scripts/check-proof-debt.sh` — exactly the one disclosed `PowSeparation.lean:40` sorry.
- `lake env lean scripts/AxiomAudit.lean` — new even-block theorems carry no `sorryAx`/new math axiom.

## Next attack

Finish objective 2's tail then objective 3:

1. Interval-integral consequences: the normalized integrand is continuous on `[2,3]`/`[3,4]`
   (polynomial over `x^N`, `x ≥ 2`), hence interval-integrable; prove each integral is `> 0`
   (nonneg + continuous + strictly positive at an interior rational) and `≤ (9/40)^N` (length one
   times the pointwise sup, via `intervalIntegral.integral_mono` / `norm_integral_le`).
2. Objective 3: the monomial integral identity `∫_a^b H_N/x^{N+1}`, isolating the `x^N` term
   (central coeff × `log(b/a)`) from the rational tail with denominators dividing `|j-N|`; clear
   with `Nat.lcmUpto N` and the exact 2-/3-adic content balances to land `A₁ + B log(3/2)`,
   `A₂ + B log(4/3)` with a common integer `B` and clearing factor `D_N`.
