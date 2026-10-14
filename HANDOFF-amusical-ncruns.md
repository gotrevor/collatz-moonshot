# HANDOFF: run-bounded near-cycles (ncbaker, Theorem MR, research §38)

- Branch: `wip/amusical-ncruns`.  Kickoff: `KICKOFF-2026-10-14-amusical-ncruns.md`.
- Target file `CollatzMoonshot/AmusicalNearCycleRuns.lean`: 0 sorries.  `RhinBound`, `numE`,
  `eRuns`, `excursionWeight` and the four statements unchanged (only the import line and the four
  proof bodies changed).  `RhinBound` is used only as the hypothesis of MR-P.
- All four (`nearCycleAt_linearForm`, `nearCycleAt_numE_le`, `nearCycleAt_numE_ge`,
  `nearCycleAt_le_of_eRuns_le`) depend only on `[propext, Classical.choice, Quot.sound]`.

## How

Helpers in `CollatzMoonshot/AmusicalNearCycleRuns/{Carry,Growth,Bootstrap}.lean`, namespace
`CollatzMoonshot.Amusical.NearCycleRuns`, stated for an abstract `x : ℕ → ℤ` obeying `2x' = 3x`
(even) and `4x' = 3x ± 1` (odd); `cntE`/`cntR` are `numE`/`eRuns` definitionally.

- **MR I (deviation: a potential instead of run bookkeeping).**  `carry_potential`: the invariant
  `p s_k + 1 − [x_k odd] p/(x_k − 1) ≤ cntR x (k+1)` (`s_k` the accumulated carry) is preserved by
  each step.  The odd-step input is `odd_step_log`: carry `≤ 1/(3z − 1) ≤ 1/(z' − 1) − 1/(z − 1)`
  (the telescoping form of `z − 1 ≥ (4/3)(z' − 1)`).  Leaving an odd run costs `p/(X − 1) ≤ 1`,
  paid by the next `E`-run start.  No run decomposition or `(3/4)^i` sums needed.
- **MR II upper (also a potential).**  `numE_potential`: with `x_k = 2^v o`, `o` odd,
  `(#E + v)(θ − 1) ≤ c(θ^r − 1)` and `log₂ x_k + v(θ − 1) ≤ c θ^r` (`c = log₂ p`,
  `r = cntR x (k+1)`).  `E`-steps preserve both exactly; an odd step decreases `x`, and landing on
  an even point opens a run whose budget `v ≤ log₂ x` is paid by the second line.  Run to `g − 1`
  and finish by hand (so the count is `eRuns p g`, not `p (g+1)`).
- **MR II lower:** as in the kickoff, `Λ > −m/p > −2/3 > −log 2`.
- **MR-P:** cases `p ≤ 1.5m`; `g = 1` (`3p/2 ≤ p + D`, so `p ≤ 2D`; Rhin needs `max a g ≥ 2`);
  main case `p < (D + m)(2g)^13.3`, `2g ≤ A_m (log p + 1)` (`two_mul_le_growthConst`), then
  `rpow_bootstrap` (via `log p + 1 ≤ 27.6 p^{1/26.6}`, `√p ≤ M D G`).  `C m` is
  `max (3m/2 + 2) (Cb m)` with `Cb` chosen from the bootstrap.

## Next steps

Nothing is owed on this kickoff.  The host merges `wip/amusical-ncruns`.
