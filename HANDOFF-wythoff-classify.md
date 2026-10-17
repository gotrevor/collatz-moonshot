# HANDOFF: wythoff-classify (Theorems N, O; Y′; the plastic 7-cycles)

Kickoff: `KICKOFF-2026-10-16-wythoff-classify.md`.  Branch `wip/wythoff-mirrorY`.

## Status

| file | sorries left |
|---|---|
| `WythoffAutomaton.lean` | 0 (Theorems N, O proved; `#print axioms thmO_iff` = propext, choice, Quot.sound) |
| `WythoffSeven.lean` | 0 (`infinite_minimalPeriod_seven` unconditional; axioms standard) |
| `WythoffMirrorY.lean` | 15 |

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

## Next

Y′ §4 (`WythoffMirrorY`), then §5, density last.
