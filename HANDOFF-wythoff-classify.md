# HANDOFF: wythoff-classify (Theorems N, O; Y′; the plastic 7-cycles)

Kickoff: `KICKOFF-2026-10-16-wythoff-classify.md`.  Branch `wip/wythoff-mirrorY`.

## Status

| file | sorries left |
|---|---|
| `WythoffAutomaton.lean` | 0 (Theorems N, O proved; `#print axioms thmO_iff` = propext, choice, Quot.sound) |
| `WythoffSeven.lean` | 0 (`infinite_minimalPeriod_seven` unconditional; axioms standard) |
| `WythoffMirrorY.lean` | 0 (`tendsto_minCount_ymPerm` proved, conditional on `WeylEquidistributionMulti` only) |

## Notes

* Theorem N: one telescoping helper `sum_coeff_mul_eq_synDiv` (any real sequence `w`) gives both
  N(1) and N(2).  For N(2) the virtual point is `w₀ = n(α − 1)` (equal to `n/(2x − 1)`), so
  `x w₀ = (α/2) n` is `xOf·(α − 1) = α/2`, no division by `2x − 1`.
* Theorem O: the downward induction `q_{d−1−m} = x^m` makes the paper's `a_k = 1` case split
  unnecessary (`a_k ∈ [−x^{m+1}, 1 − x^{m+1}] ⊂ (−1, 1)` strictly).
* Box gotcha: `lake env lean` occasionally fails with "Too many open files" (transient); retry.
* Scratch files live in `tmp/scratch/` (gitignored); `tmp/tools/fill.py FILE NAME PROOF`
  splices a proof body into the first `sorry` of a named theorem.

* Seven labels: each `K_i` is an exact linear form in the step phases (`evenStep`, `oddStep`),
  remainder 0 mod the cubic (computed with `tmp/tools/poly.py`, a tiny Q[x,…] division helper);
  no torus coordinates.  Translation lemma split into `tstep1..6` over a `TCtx` bundle: one
  theorem with all steps hit the 200k heartbeat limit.

* Y′ §4-§5: Theorem M transfers verbatim; the phase identities are
  `linear_combination (∓(s+1)/2) * g_mul_alphaY (+ W′ s * cubic)`.  `four_eq` uses `τ = −t` in
  Theorem Y's `yPhase4_of_one` / `_of_neg_one`.  (H2) uses the chain
  `x^i (A(s+1) + 6/5) ≤ W′^{i+1}(s) + 11/5` (`1 + xK ≤ K` at `K = 11/5`), `s ∈ {1, 3}` by
  `ymEvenEval` / `ymOddEval`.  `setCount` helpers copied locally (`WythoffLine` is not imported).

* Y′ density: no polygon work at all.  `wy_mirror_eq_neg` (any `α > 1`):
  `W_β(n) = −W_α(−n − 1) − 1`, i.e. `W_β = σ W_α σ`, `σ(m) = −m − 1`.  So the return word of
  `2k − 1` under `W′` is Theorem Y's word of `−2k`, and Y's phase lemmas
  (`wy_two_mul_odd_iff`, `wy_wy_two_mul_odd_iff`, `wy_three_even_iff_strip`) already hold for all
  integer `k`; the phase of `−k` is Weyl at frequencies `−(c₀, c₁)` (`ymTheta`,
  `LinearIndependent.units_smul`), with Y's own `yWord`, `yVol`; Y's sandwich at `−2k` gives
  `|R′ − αxʲk| < 3`.

## Next

All 46 kickoff statements are proved (`#print axioms` of `thmO_iff`, `first_step_odd_iff`,
`infinite_minimalPeriod_seven`, `minimalPeriod_alphaP_twenty`, `tendsto_minCount_ymPerm`:
propext, choice, Quot.sound).  The kickoff's out-of-scope list is the next layer.  The
conjugacy `wy_mirror_eq_neg` suggests the G mirror density (`WythoffLine`) and any future mirror
could be derived from the main side directly rather than re-proved.

HEAD at handoff: see `git log` (branch `wip/wythoff-mirrorY`); no uncommitted edits.
