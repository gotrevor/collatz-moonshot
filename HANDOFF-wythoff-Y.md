# HANDOFF: Theorem Y and the golden member (kickoff `KICKOFF-2026-10-16-wythoff-Y.md`)

Branch `wip/wythoff-Y`.  Build: `lake build CollatzMoonshot.WythoffSporadic CollatzMoonshot.WythoffGolden`.
The box hits spurious "Too many open files" often; `tmp/scratch/build.sh` / `chk.sh` retry it.

## Done
* §1 (Sporadic): `yRoot_spec` (IVT), `yRoot_unique`, `yRoot_bounds` (strict monotonicity),
  `irrational_yRoot`, `linearIndependent_yRoot` (minpoly = the cubic via
  `irreducible_of_degree_le_three_of_not_isRoot` + `isInteger_of_is_root_of_monic`), `irrational_alphaY`.
* §2 (Sporadic): polygon lemmas by explicit certificates (`(1 + x)(Δ_1 − 1) = (2 − x)(Δ′ − 1) +
  g(x² + x + 3)(1 − f₁) + x(2x − 1)`, mod `(x + 1)·cubic`; `Δ_{−1} + 1 = g(1 + x)(1 − f₁) +
  (2 − x)(1 − f₂)`), phase identities (`g α = 4`), `wy_iterate_three_sub_mem`,
  **`wy_iterate_four_eq`** (the recurrence), `exists_even_iterate_Y`.

## Next
`le_wy_iterate_of_odd_run_Y` (sandwich `W^{i+1} + 1 ≥ x(Wⁱ + 1)`), §3, then Golden §5/§6, densities last.
