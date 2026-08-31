# HANDOFF 2026-08-31 — sink closed + K=1 content lemma complete + K=1 clearing proved

- **Branch:** `main`  **HEAD:** `5322ee9`  **Tree:** clean (nothing uncommitted). Not pushed.
- `lake build` green (8764 jobs). `bash scripts/check-proof-debt.sh` = **one** disclosed sorry
  repo-wide: `RhinLiteApprox.lean` (`rhinLiteLIMeasure`).  `PowSeparation.lean` is sorry-free.

## Arc of this session (6 green commits, `3da2219 → 5322ee9`)

1. **`3da2219` — sink `sep_two_three` CLOSED** (was the disclosed sorry at `PowSeparation.lean:40`).
   Proved modulo the single cited `Assumed.rhin_1987_log_two_three_measure` axiom via a
   threshold-parametric reduction: `sep_of_linear_form_poly_threshold` (crossover threshold `K` free),
   `crossover_exp_450` (`3^14·k^14 ≤ 2^(k/3)` for `k ≥ 450`), `sep_two_three_small_450`
   (`native_decide` on `6 ≤ k < 450`), instantiated at `κ=14, c=1/3^14, K=450` with
   `log23_effective_measure_concrete` (moved into `PowSeparation.lean`; imports `Assumed.Rhin1987`).
   `#print axioms sep_two_three` = trust base + Rhin axiom + 3 `native_decide` artifacts. The whole
   two-block exclusion `le_two_blocks_not_acyclicParadoxical` inherits this clean ledger.
2. **`43ebbf4`** — decomposed the K=1 content lemma into named nodes; combined
   `rhinLiteEvenPolynomialZ_content` (`12^{N−j} ∣ coeff_j`) PROVED from the 2-/3-adic parts via
   `IsCoprime (4^k) (3^k)`. Numerically verified true on the exact degree-4000 base polynomial first.
3. **`950b391` — 3-adic content PROVED** (`rhinLiteEvenPolynomialZ_three_adic_content`): the
   `Dvd3Adic` coefficientwise `(3,X)`-order predicate, superadditive over products
   (`Dvd3Adic_mul` via `coeff_mul` + `Finset.dvd_sum`); factor orders `(1,0,0,1,2,2)` sum to N.
4. **`5406f88` — 2-adic content PROVED** (`rhinLiteEvenPolynomialZ_two_adic_content`): the node I'd
   flagged as Newton-polygon-hard turned out **elementary** — grouping factors into squares
   (`(X−2)² ∈ (4,X)`, `Q₅² ∈ (4,X)³`) captures the cross-terms; `Dvd4Adic` orders
   `(0,w₂t,2w₃t,2w₄t,3w₅t,4w₆t)` sum to exactly N=2000t. **So the content lemma is now fully
   machine-checked** (trust-base-only ledgers).
5. **`5322ee9` — K=1 clearing lemmas PROVED** in `RhinLiteLogForm.lean` (sorry-free): `content_zpow_isInt`
   (`c·e^{j−N} ∈ ℤ` for `e ∣ 12` given `12^{N−j} ∣ c`), `tail_term_cleared_K1`, and
   `lcm_cleared_log_form_K1` (the `D_N = lcmUpto N` log form, taking the content as a hypothesis).
   These are the general clearing lemmas with a **decaying** remainder (`E_N = lcmUpto N·(9/40)^N → 0`,
   `K=1<τ`), fixing the `12^N` over-clearing diagnosed last session.

## State of the crux — `rhinLiteLIMeasure` (the only open sorry, `RhinLiteApprox.lean`)

TRUE (Rhin 1987). Its purpose is now to **retire** the cited `rhin_1987_log_two_three_measure` axiom.
The `12^N` route is dead (scaling bug `overcleared_remainder_ge_one`); the K=1 route is now well under
way. Everything needed for the K=1 clearing is proved:
- Content: `rhinLiteEvenPolynomialZ_content` (`12^{N−j} ∣ coeff_j`) ✅
- Clearing: `lcm_cleared_log_form_K1`, `tail_term_cleared_K1`, `content_zpow_isInt` ✅
- Mechanism (from before): `logForm_conditional_lower`, `rhinLite_forms_bounded` ✅

## Next lap (priority order) — see `PENDING_WORK.md` "★ K=1 content lemma COMPLETE"

1. **Instantiate `lcm_cleared_log_form_K1` at `P = rhinLiteEvenPolynomialZ t`** (endpoints `(2,3)` and
   `(3,4)`) feeding `hcontent := rhinLiteEvenPolynomialZ_content t`. This yields the K=1 versions of the
   two concrete log forms (a `rhinLiteEven_two_log_forms`-analogue with `D_N = lcmUpto N`, common
   `B = lcmUpto N · centralCoeff`). Need `hdeg`/`hN`: from `rhinLiteEvenPolynomialZ_map_real_natDegree`
   (degree `2N`) and `N ≤ 2N`. This is mechanical wiring — a clean, tractable next lap.
2. Re-derive `rhinLite_forms_bounded` with the smaller `D_N` (now `E_N = lcmUpto N·(9/40)^N → 0`), so
   `logForm_conditional_lower` becomes non-vacuous (needs `lcmUpto N ≤ 4^N` — mathlib `Nat.lcmUpto`
   Chebyshev bound — and `4 < e^{τ}=40/9`).
3. Non-vanishing determinant of three consecutive `(B, A₁, A₂)` triples (nonzero integer ⇒ `n ≠ 0`);
   then assemble `rhinLiteLIMeasure` with `μ ≈ 7.9`.

## Bookkeeping

- `scripts/AxiomAudit.lean`: added `sep_two_three`(+helpers), the three content lemmas, and the three
  K=1 clearing lemmas.
- `scripts/check-proof-debt.sh`: gate updated to pin the single sorry in `RhinLiteApprox.lean` only
  (PowSeparation.lean sorry-free). Count within RhinLiteApprox may grow as the crux decomposes.
- Docs current: `README`, `STATUS`, `PENDING_WORK`, `FRONT-A-RHIN-LITE-SCALING-2026-08-31.md`.
