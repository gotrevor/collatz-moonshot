# HANDOFF: wythoff-classify (Theorems N, O; Y′; the plastic 7-cycles)

Kickoff: `KICKOFF-2026-10-16-wythoff-classify.md`.  Branch `wip/wythoff-mirrorY`.

## Status

| file | sorries left |
|---|---|
| `WythoffAutomaton.lean` | 0 (Theorems N, O proved; `#print axioms thmO_iff` = propext, choice, Quot.sound) |
| `WythoffSeven.lean` | 0 (`infinite_minimalPeriod_seven` unconditional; axioms standard) |
| `WythoffMirrorY.lean` | 1: `tendsto_minCount_ymPerm` (the conditional Y′ density) |

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

## Next

The last sorry: `WythoffMirrorY.tendsto_minCount_ymPerm` (Weyl-conditional density; kickoff §5,
≈ 450 lines).  Template: `WythoffSporadic` §Density (`yPh`, `yWord`, `yPh_mem_yWord`,
`returnTime_yPerm_eq_iff`, `yReturn_bound`, `tendsto_returnCount_yPerm`, `densityY_sum_eq`).
Plan: for `s = 2k − 1` show the mirror cylinder `O Eʲ` is cut out by the same polygons in
`(Int.fract (k·yc0), Int.fract (k·yc1))` (Theorem M: `ymF1 = 1 − {kα}`-type phases), reuse
`tendsto_yWordCount`, then `minCount_ymPerm_add` and `densityY_sum_eq`.  Read how
`minCount_yPerm` density is assembled at the end of `WythoffSporadic.lean` first.

HEAD at handoff: see `git log` (branch `wip/wythoff-mirrorY`); no uncommitted edits.
