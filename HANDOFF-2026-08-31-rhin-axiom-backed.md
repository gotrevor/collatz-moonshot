# HANDOFF 2026-08-31 — Rhin-lite obj 4: scaling bug found, effective measure now axiom-backed

- **Branch:** `main`  **Tree:** clean after commits (not pushed).
- `lake build` green (8764 jobs). `bash scripts/check-proof-debt.sh` = two disclosed sorries:
  `PowSeparation.lean:40` (`sep_two_three`) and `RhinLiteApprox.lean:380` (`rhinLiteLIMeasure`).

## Arc of this session (five green commits)

1. **`RhinLiteApprox.lean` created** — wired the simultaneous-approximation criterion as far as
   elementary algebra allows: `linForm_eq_log23` (change of basis to the Baker linear form),
   `elim_identity`, and `log23_effective_measure` (the `log₂3` measure in `hLF` shape).
2. **Size bridge proved** — `rhinLiteEvenPolynomialZ_eval_real`, `rhinLiteEven_logForm_integrand`
   (`H_N/x^{N+1} = normalized/x`), `intervalIntegrable_rhinLiteEven_logForm`,
   `rhinLiteEven_logForm_small_23/_34` (`0 < ∫ H_N/x^{N+1} ≤ (9/40)^N`).  All trust-base clean.
3. **Transference mechanism proved** — `logForm_conditional_lower` (`n ≠ 0 ⇒ |Λ| ≥ (1 −
   (|q|+|r|)E)/B`) and `rhinLite_forms_bounded` (data + size packaging).  Trust-base clean.
4. **Scaling bug diagnosed** (the route-decisive finding) — the `12^N`-cleared forms CANNOT prove
   `rhinLiteLIMeasure`: Wu's clearing rate `K = 1 + log 12 ≈ 3.49` exceeds the remainder decay
   `τ = log(40/9) ≈ 1.49`, and Wu (Math. Comp. 72 (2003) Thm 2) needs `τ > K`.  In-kernel witness
   `overcleared_remainder_ge_one` (`1 ≤ lcmUpto N · 12^N · (9/40)^N` ∀N), so the mechanism is
   vacuous at every index.  Fix recorded (`FRONT-A-RHIN-LITE-SCALING-2026-08-31.md`): structural
   clearing `H_N ∈ (12,x)^N ℤ[x]` ⇒ `D_N = lcmUpto N`, `K = 1 < τ`, `μ ≈ 7.9`.
5. **Effective measure now axiom-backed** (DIRECTION option (a), corpus-recommended) —
   `Assumed/Rhin1987.lean` states `rhin_1987_log_two_three_measure` (`|u₀+u₁log2+u₂log3| ≥ 1/H^14`,
   `H = max(|u₁|,|u₂|) ≥ 2`; Rhin 1987, read firsthand, `papers/`), and `log23_effective_measure`
   is **proved from it** (`κ=14`, `c=1/3^14`) — clean ledger `[…, rhin_1987_log_two_three_measure]`,
   no `sorryAx`.

## State of the crux(es)

- `rhinLiteLIMeasure` (disclosed sorry, novel target): TRUE (Rhin), but the `12^N` forms can't
  reach it.  Its remaining purpose is to *retire* the axiom via the K=1 structural clearing.  The
  entire elementary apparatus around it (size bridge, elimination, conditional lower bound, data
  packaging) is proved; only the K=1 clearing + non-vanishing determinant + `lcmUpto` asymptotic
  remain — a genuine multi-lap ANT expedition.
- `sep_two_three` (disclosed sorry, sink): now one **elementary** step from `log23_effective_measure`.
  Blocker: `κ=14` makes `sep_of_linear_form_poly`'s hard-coded `k ≥ 130` crossover too small
  (`k^14 ≤ (1/3^14)·2^{k/3}` first holds around `k ≈ 360`).  Close by either (i) extending the
  finite `native_decide` check from `k<130` to `k≈360` (heavy: `3^360` ~172 digits), or (ii) adding
  a parametric-threshold variant of `sep_of_linear_form_poly`.  Computation/interface, not
  Diophantine.

## Next lap options (priority order)

1. **Close `sep_two_three`** via option (ii) above — a `sep_of_linear_form_poly`-with-parametric-`K`
   lemma in `PowSeparation.lean`, then instantiate with `log23_effective_measure`'s `κ=14, c=1/3^14`
   and a `native_decide` finite check on `6 ≤ k < K`.  This would make the whole two-block exclusion
   machine-checked modulo one cited Rhin axiom (Hercher-style) — a clean campaign milestone.
2. **Retire the axiom** — the K=1 structural clearing for `rhinLiteLIMeasure`: prove
   `12^{N−j} ∣ coeff_j(H_N)` (i.e. `H_N ∈ (12,x)^N ℤ[x]`; content balances already numeric in
   `RhinLite.lean`), redo `lcm_cleared_log_form` with `D_N = lcmUpto N`, then the non-vanishing
   determinant + `lcmUpto ≤ 4^N`.  Multi-lap.

## Bookkeeping

- `scripts/AxiomAudit.lean`: added `linForm_eq_log23`, `elim_identity`,
  `rhinLiteEven_logForm_integrand`, `_small_23/_34`, `logForm_conditional_lower`,
  `rhinLite_forms_bounded`, `overcleared_remainder_ge_one`, `log23_effective_measure`,
  `rhin_1987_log_two_three_measure`.
- `scripts/check-proof-debt.sh`: generalized to pin sorry locations (PowSeparation + RhinLiteApprox).
- Docs updated: `README`, `STATUS`, `DIRECTION` (pointer only), `FRONT-A-RHIN-LITE`,
  `FRONT-A-RHIN-LITE-SCALING-2026-08-31.md`, `PENDING_WORK`.
