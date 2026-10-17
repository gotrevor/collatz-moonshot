# HANDOFF: Theorem Y and the golden member (kickoff `KICKOFF-2026-10-16-wythoff-Y.md`)

Branch `wip/wythoff-Y`.  Build: `lake build CollatzMoonshot.WythoffSporadic CollatzMoonshot.WythoffGolden`.
The box hits spurious "Too many open files" often; `tmp/scratch/build.sh` / `chk.sh` retry it.

## Status: DONE

Both files are sorry-free; all 77 ratified declarations unchanged vs `4386760` (header-text
diff).  With the proved base files of `wip/wythoff-solvable` checked out temporarily (not
committed), `tendsto_minCount_yPerm`, `wy_iterate_four_eq`, `yPerm_infinitelyManyInfiniteOrbits`,
`tendsto_minCount_goldPerm`, `minCount_goldPerm_eq` print `[propext, Classical.choice, Quot.sound]`.
On this branch alone they show `sorryAx`, inherited only from the four black-box base files.
`WeylEquidistribution(Multi)` stay hypotheses.

## Done
* §1 (Sporadic): `yRoot_spec` (IVT), `yRoot_unique`, `yRoot_bounds` (strict monotonicity),
  `irrational_yRoot`, `linearIndependent_yRoot` (minpoly = the cubic via
  `irreducible_of_degree_le_three_of_not_isRoot` + `isInteger_of_is_root_of_monic`), `irrational_alphaY`.
* §2 (Sporadic): polygon lemmas by explicit certificates, phase identities (`g α = 4`),
  `wy_iterate_three_sub_mem`, **`wy_iterate_four_eq`** (the recurrence), `exists_even_iterate_Y`,
  run bound `le_wy_iterate_of_odd_run_Y`.
* §3 (Sporadic): `hyp_yPerm`, classification, exact count, `⌊3X/8⌋` lower bound, infinitely
  many infinite orbits.
* §5/§6 (Golden): all, including the three 1D-Weyl densities.
* §4 (Sporadic density, `section Density`).  Coordinates `(u, w) = ({k c₀}, {k c₁})`,
  `c₀ = α/2`, `c₁ = xα/2` (`yPh`).  Word of `2k` (`yPh_mem_yWord`, `returnTime_yPerm_eq_iff`):
  `E` iff `u < 1/2`; `E O` iff `u ≥ 1/2` and `yW2 u w = w − xu + x ∉ (1/2, 1]`; `E O O E` iff
  `w ∈ [yMu u, yMu u + yDelta)`, `yDelta = 1/(2(1 + x))` (from `Δ′ ∈ (0, 1]`,
  `wy_iterate_three_odd_iff`); else `E O³`.  The strip lies inside the `E O O` parallelogram
  (`yMu_lower`, `yMu_upper`: equality only at `u = 1`).  Areas by `volume_shear` (Fubini via
  `volume_preserving_finTwoArrow` + `Measure.prod_apply` + translation invariance):
  `(1/2, 1/4, 1/(4(1+x)), x/(4(1+x)))`; frontiers null by `Convex.addHaar_frontier` on the
  three convex pieces and `frontier_sdiff_subset'`.  Sandwich `|R(2k) − αxʲk| < 2`
  (`yRun_sandwich`, invariant `|e| < 2` since `3x < 2`).  Counting as `WythoffLine`'s
  `tendsto_returnCount_div`, with `αxʲ ≥ 2` replacing `≥ 4`.  Closed form
  `densityY_sum_eq`: residual after `field_simp` is `32(−5 − 5x² − 4x³)·cubic`.

## Gotchas
* `linear_combination` coefficient after `field_simp`: read the residual, divide by the cubic
  (tiny Fraction poly-division in Python; no sympy on the box).
* `set S : Set ℤ := {n | n % 2 = 0}` did not abstract through a rewritten lemma; omega then
  saw two atoms.  Use the literal set.
* `rw` with `volume_shear` needs the shear function given explicitly (higher-order pattern).
* Counting helpers `yTendsto_floor_linear(_div)`, `yTendsto_comp_div` are `y`-prefixed copies of
  the `WythoffGeneral` ones on `wip/wythoff-solvable`, so the merge does not clash (checked:
  the merged build is green).
