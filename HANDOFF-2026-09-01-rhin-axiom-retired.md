# HANDOFF 2026-09-01 — Rhin 1987 axiom RETIRED; `sep_two_three` proved from Rhin-lite, axiom-free

## State
- Branch `main`, working tree to be committed this lap (see commit message).  Nothing to push.
- `src/` (the `CollatzMoonshot` lib) is **sorry-free** and the two-block exclusion path now carries
  **no literature axiom**.

## The fork the operator posed, and the verdict
Fork: re-wire `sep_two_three` onto our proved `rhinLiteLIMeasure` instead of the cited Rhin 1987
axiom; confront the exponent-435 crossover head-on; refute if infeasible.

1. **Direct re-wiring — REFUTED.**  `rhinLiteLIMeasure` is `∃ κ c` with `c = 1/(2C)`,
   `C = (396/5)^(6000+N₀)·6^κ`, and `N₀` is the classical threshold of `lcmUpto_le_pow_eventually`
   (`isLittleO.def` → `Filter.eventually_atTop`).  With `c` opaque there is no concrete `K`, and the
   finite check `hfin` of `sep_of_linear_form_poly_threshold` cannot be stated, let alone decided.
2. **Explicit-constant re-wiring — FEASIBLE, and DONE** (`CollatzMoonshot/FrontA/RhinLiteSep.lean`):
   - `lcmUpto(2000t) ≤ (22/5)^(2000t)` for **all** `t ≥ 1` (so `N₀ = 0`): eight monotone block
     certificates by `decide +kernel` for `t ≤ 30` (`lcmUpto_block_le` + `lcmUpto_dvd_of_le`), and
     mathlib Chebyshev `ψ N ≤ N log 4 + 2√N log N` for `N ≥ 62000` with the subexponential term
     absorbed by `4 log s ≤ s/11`, `s = √N ≥ 248` (`lcmUpto_le_pow_of_ge`, derivative-free).
   - `κ = 436` (`(100/99)^436 ≥ 396/5`, kernel-checked; `435` fails), `C = (396/5)^6000·6^436`,
     `c = rhinLiteSepC`, `log₂(1/c) ≈ 38972`.  `rhinLite_selection_envelope_of_majorant` and
     `rhinLiteLIMeasure_of_envelope` are the generic (constants-abstracted) versions of the two
     existing assembly lemmas; `rhinLiteLIMeasure_explicit` instantiates them.
   - `rhinLite_log23_measure`: on the window, the form `(m−2k)·log(3/2) + (m−k)·log(4/3)` has
     height `≤ k` (`k < m ≤ 2k`), so `Λ ≥ c/k^436` with no extra loss.
   - Crossover `K = 141000 = 3·47000` (`crossover_exp_of_base`, generic induction with `5κ ≤ K`;
     base case `2·141000^436·396^6000·6^436 ≤ 2^47000·5^6000` by `decide +kernel`, margin 133 bits).
   - Finite range `450 ≤ k < 141000`: five consecutive-convergent brackets of `log₂3`
     (`306/665`, `665/15601`, `15601/31867`, `31867/79335`, `79335/111202`) through the all-integer
     interface `sep_of_bracket_nat` (inner same-side fractions give `min(bθ−a, c−dθ) ≥ min(1/b',1/d')`;
     scale `j` with `3j ≤ k`, `2b' ≤ 2^j`).  Eight power certificates, largest `2^478245 < 3^301739`
     (144k digits), all `decide +kernel` — `#print axioms` = `[propext]`.  `k < 450` is the existing
     `native_decide` table.
   - `sep_two_three_rhinLite`, and the canonical `sep_two_three` := it; `bd_reduction` moved here
     verbatim; `Paradoxical.lean` now imports `RhinLiteSep`.
3. **κ-sharpening (operator point 3) — REFUTED as low-leverage.**  `C ≈ 10^11730` is fixed by the
   `2000`-index spacing + 3-index non-vanishing window; even Hanson `lcm < 3^n` (κ ≈ 11) moves `K`
   only `139k → 104k`, and the convergent denominators jump `190537 → 10590737`, so every
   `K < 190537` costs the same certificates.

## Axiom audit (real `#print axioms`, run on the compiled module)
`sep_two_three_rhinLite` and `rhinLiteLIMeasure_explicit`: `[propext, Classical.choice, Quot.sound]`
plus the Rhin-lite tower's `native_decide` certificates (`rhinLiteI₁_ratio_base`,
`rhinLiteRootLeft_ge_three`, `rhinLite_boundProduct_certificate(_tight)`,
`rhinLite_cauchy_radius_certificate`, `rhinLite_critical_sign_change`, `rhinLite_factorBound_nonneg`,
`rhinLite_positiveRootLeft`, `rhinLite_rootBracket_lt`, `rhinLite_rootBrackets_separated`,
`seventeen_pow_scale_le_rhinLiteBlockTerm`) and, for `sep_two_three_rhinLite`, the `k < 450` table
(`sep_two_three_finite_check_450`, `sep_two_three_small_450`).  **No `sorryAx`, no
`rhin_1987_log_two_three_measure`.**

## Housekeeping
- `Assumed/Rhin1987.lean` → `wip/Rhin1987.lean` (git mv); the old `κ = 14` route
  (`log23_effective_measure_concrete`, `log23_effective_measure`, old `sep_two_three`) →
  `wip/RhinAxiomRoute.lean` (not compiled; revival notes in its header).
- `PowSeparation.lean` keeps the elementary engine only; header rewritten.  `RhinLiteApprox.lean`
  header de-staled (it claimed `rhinLiteLIMeasure` was a sorry and that `log23_effective_measure`
  was derived from it); README / STATUS / PENDING_WORK / `check-proof-debt.sh` / `AxiomAudit.lean`
  updated.

## Kernel-vs-native facts learned (for the corpus)
- `decide +kernel` handles `2^478245 < 3^301739` (~2 s) and `Nat.lcmUpto 60000·5^54000 ≤ 22^54000`
  with `set_option maxRecDepth 100000` + `set_option exponentiation.threshold`; the 5M-digit
  `2^16785921 < 3^10590737` hits the kernel numeral cap (`LEAN_NAT_MAX_SIZE`) but passes
  `native_decide` in seconds.  `∀ t < 31, lcmUpto (2000t)…` as ONE kernel `decide` is too slow
  (>2 min); split into monotone blocks.
- State kernel certificates in the *exact* syntactic shape the consumer needs
  (`Nat.lcmUpto (2000 * 11) * 5 ^ (2000 * 8) ≤ …`), otherwise `exact` makes the elaborator evaluate
  the big literal and dies on recursion depth.

## Next steps
- Fresh direction: the remaining cited axioms (`rozier_terracol_3_2`, `Assumed/Cycles.lean`,
  `Assumed/Computation.lean`, …) — inventory via `scripts/AxiomAudit.lean`.
- Optional: convert the Rhin-lite tower's `native_decide` certificates to `decide +kernel` where
  operand sizes allow, to shrink `sep_two_three`'s ledger to the bare trust base.
- No in-flight Aristotle job.
