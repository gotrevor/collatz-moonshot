# HANDOFF: the two primes decouple (Lemma D, Corollary MD), DONE

- Branch: `wip/amusical-decouple`.  Kickoff: `KICKOFF-2026-10-14-amusical-decouple.md`.
- Target file `CollatzMoonshot/AmusicalDecouple.lean`: 0 sorries, ratified statements and
  `countBelow` unchanged (imports, proof bodies, and "Target" → "Proved" in docstrings).
- `tendsto_density_inter_of_two_three` (Lemma D), `orbitMin_density_of_survivor_densities`
  (Corollary MD), `not_formalMin_of_three_dvd`, `infinitelyManyOrbits_of_ray` all depend only on
  `[propext, Classical.choice, Quot.sound]`.  Full `lake build` green.
- `AmusicalGlobal.lean`: `private` removed from `FwdWindowSurvivor`, `BwdWindowSurvivor`,
  `tendsto_fwdWindowSurvivor_density`, `tendsto_bwdWindowSurvivor_density`,
  `isOrbitMin_iff_survivors` (allowed by the kickoff).  Nothing else there changed.

## How

`AmusicalDecouple/Density.lean` (namespace `CollatzMoonshot.Amusical.Decouple`, pure `ℕ`-set
density, no Collatz content).  `cnt` is definitionally `countBelow`; `EvPer S p N` is the
kickoff's periodicity hypothesis.

- `tendsto_cnt_div_of_evPer`: an eventually `p`-periodic set has density `blockCnt / p`
  (`cnt S (X + p) = cnt S X + blockCnt` above `N`, then a bounded-error-to-density lemma).
- `blockCnt_inter_of_coprime` (CRT via `Finset.card_bij`, `Nat.chineseRemainder`) and
  `tendsto_cnt_inter_of_coprime`: coprime-period sets are independent.
- `tendsto_of_sandwich`: a two-parameter squeeze (`tendsto_order`), used twice.
- Step (i) was done differently from the kickoff: no residue classes mod `2ⁿ`.  For any
  `2`-power-periodic `P` of density `d`, `cnt(P ∩ B) ≤ cnt(P ∩ B_L)` and
  `cnt(P ∩ B) ≥ cnt(B) − cnt(Pᶜ ∩ B_L)`, both sides converge by CRT to `d·b_L` and
  `β − (1−d) b_L`, and both tend to `dβ` (`tendsto_cnt_inter_iInter`).  Step (ii) applies this
  with `P = A_L` (`tendsto_cnt_iInter_inter`).

`AmusicalDecouple/Windows.lean`: eventual periodicity of the real windows was not heavy.
`isWin_iff_good_of_large` is a verbatim copy of the private `windowSurvivors_iff_good_of_large`
(above `4^L 3^L (windowBound L + 1)`, window survival is a function of the branch word), and the
words are `4^L`- / `3^L`-periodic (`amusicalForwardWord_natCast_mod`).  So `evPer_fwdWin`
(period `2^(2L)`) and `evPer_bwdWin` (period `3^L`) are a few lines each.  `pf * pb =
minimaConstant` comes from `windowDensityLimit` and uniqueness of limits.

## Next steps

Nothing is owed on this kickoff.  The host merges `wip/amusical-decouple`.
