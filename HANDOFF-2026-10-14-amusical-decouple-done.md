# HANDOFF 2026-10-14: the two primes decouple (Lemma D, Corollary MD), DONE

- Branch: `wip/amusical-decouple`.  HEAD: `0f5a44e`, plus this note's commit.
- Scope: close every `sorry` in `CollatzMoonshot/AmusicalDecouple.lean`.  Met: 0 sorries, full
  `lake build` green, ratified statements unchanged.  All four targets depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Proved: `tendsto_density_inter_of_two_three` (Lemma D),
  `orbitMin_density_of_survivor_densities` (Corollary MD), `not_formalMin_of_three_dvd`,
  `infinitelyManyOrbits_of_ray`.
- Helpers in `CollatzMoonshot/AmusicalDecouple/{Density,Windows}.lean`.
- Details: `HANDOFF-amusical-decouple.md`.

## Next steps

Nothing is owed on this kickoff.  The host merges `wip/amusical-decouple`.  `box done` has been
signalled and the host confirmed the scoped target is clean.
