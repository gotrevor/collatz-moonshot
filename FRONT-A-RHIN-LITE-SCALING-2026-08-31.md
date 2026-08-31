# Rhin-lite objective 4 — scaling diagnosis (2026-08-31)

## Summary

The simultaneous-approximation criterion (`rhinLiteLIMeasure`) **cannot be proved from the
`12^N`-cleared integer log forms** produced by `RhinLiteLogForm.lean`.  The clearing
`D_N = lcmUpto N · 12^N` over-clears: its rate `K` exceeds the remainder decay `τ`, so the cleared
linear-form value grows instead of decaying.  This is the "27/10 does not decay" issue the prior
handoff flagged, now diagnosed precisely and witnessed in-kernel.

This is **not** a defect in objectives 1–3 (the polynomial/integral/log-form identities are all
correct and stay). It is a defect in the *choice of clearing factor* for the measure step, and it
is fixable.

## The numbers (Wu, Math. Comp. 72 (2003), Theorem 2)

Wu's criterion: with clearing `D_n`, remainder `I_n`, coefficient growth, define
`K = lim (1/n) log D_n`, `τ = −lim (1/n) log I_n`, `τ⁽⁰⁾ = lim (1/n) log ‖coeff‖`.  A finite linear
independence measure `μ = (τ⁽⁰⁾ + K)/(τ − K)` results **iff `τ > K`**.

For the coarse Rhin-lite kernel:

| quantity | value | source |
|---|---|---|
| `τ` (remainder decay) | `log(40/9) ≈ 1.492` | `rhinLiteEven_logForm_small_23/_34`: `I_N ≤ (9/40)^N` |
| `τ⁽⁰⁾` (coeff growth) | `≈ log 18 ≈ 2.89` | `rhinLiteEvenPolynomialZ_centralCoeff_bounds`: `B_N ≤ 18^N` |
| `K` **as formalized** (`D_N = lcmUpto·12^N`) | `1 + log 12 ≈ 3.485` | `RhinLiteLogForm` clearing |
| `K` **correct** (`D_N = lcmUpto`) | `1` | Wu, `Δ=1` reading |

- Formalized: `τ − K ≈ 1.492 − 3.485 < 0` ⟹ **no measure** (value grows like `(27/10·e)^N`).
- Correct: `τ − K ≈ 1.492 − 1 = 0.492 > 0` ⟹ `μ ≈ (2.89 + 1)/0.492 ≈ 7.9` (finite; cf. Rhin's
  optimal `7.616` with the sharp kernel).

## Machine witness

`overcleared_remainder_ge_one (N)` proves, trust-base clean,
`1 ≤ lcmUpto N · 12^N · (9/40)^N`.  So the cleared remainder `E_N ≥ 1` for every `N`, hence the
(correct) mechanism lemma `logForm_conditional_lower` at `E = E_N` yields
`1 − (|q|+|r|)·E_N ≤ 0` — a vacuous bound — for every index.  The over-clearing is therefore fatal
to *this* route, provably.

## Why `12^N` is wrong, and the fix

The endpoint powers `x^{j−N}` (negative for `j < N`) at `x ∈ {2,3,4}` need clearing.
`RhinLiteLogForm` cleared them with a **global `12^N` multiplier** (`endpoint_pow_dvd_twelve_pow`,
`twelve_pow_mul_zpow_isInt`).  But `H_N ∈ (12,x)^N ℤ[x]` (the content balance already proved in
`RhinLite.lean`): each coefficient `c_j` is divisible by `12^{N−j}`, so `c_j · x^{j−N}` at
`x | 12` is **already an integer** — the endpoints clear *structurally*, and only `lcmUpto N` (for
the `1/(j−N)` factors) remains.  This is exactly Wu's `Δ=1`, `K=1` construction.

**Next step (the corrected objective 4):** re-derive the integer log form with `D_N = lcmUpto N`
only, exploiting `H_N ∈ (12,x)^N ℤ[x]` to clear endpoints from the coefficient content instead of a
global `12^N`.  Concretely:
1. Prove the content lemma `12^{N−j} ∣ coeff_j (H_N)` (or `H_N ∈ (12,x)^N ℤ[x]`) — the balances are
   already checked numerically in `RhinLite.lean`; lift to the divisibility statement.
2. Redo `tail_term_cleared` / `lcm_cleared_log_form` with the structural clearing: show
   `lcmUpto N · coeff_j · (b^{j−N} − a^{j−N})/(j−N) ∈ ℤ` using `12^{N−j} ∣ coeff_j` and `b,a ∣ 12`.
3. The new forms have `L_i = lcmUpto N · I_i`, `E_N = lcmUpto N · (9/40)^N = (e·9/40)^N → 0`
   (`e·9/40 ≈ 0.611 < 1`), so `logForm_conditional_lower` becomes non-vacuous and the transference
   goes through with `μ ≈ 7.9`.
4. Then attack the non-vanishing determinant + the `lcmUpto ≤ 4^N` bound (`K = 1` needs only
   `lcmUpto N ≤ C^N` with `C < e^{τ}` — mathlib `Nat.lcmUpto`/Chebyshev supplies `lcmUpto N ≤ 4^N`,
   and `4 < e^{1.492} ≈ 4.45`, so even the crude `4^N` bound keeps `τ > K`).

**Alternative (per DIRECTION.md option (a) / corpus recommendation):** disclose one named
Rhin-grade axiom (`|u₀ + u₁log2 + u₂log3| ≥ H^{−13.3}`, Rhin 1987) and keep the machine-checked
reduction (`log23_effective_measure`, the PowSeparation pipeline) — the same doctrine the repo uses
for the Hercher bound.  This is the proportionate move if the structural re-derivation proves too
long; the coarse-kernel construction is then independent corroboration, not the proof.

## Status of the crux

`rhinLiteLIMeasure` remains an honest disclosed `sorry`.  It is a TRUE statement (Rhin 1987); the
`12^N`-cleared forms cannot reach it (proved above); the K=1 structural route can (μ ≈ 7.9).  Do
not weaken or fake it.
