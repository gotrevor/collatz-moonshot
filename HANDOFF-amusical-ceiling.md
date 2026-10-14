# HANDOFF: amusical survivor ceiling (C2 / C2′), DONE

- Branch: `wip/amusical-ceiling`.  Kickoff: `KICKOFF-2026-10-14-amusical-ceiling.md`.
- Target file `CollatzMoonshot/AmusicalSurvivorCeiling.lean`: 0 sorries, ratified statements
  unchanged (only the import line and the proof bodies changed; docstrings now say "Proved").
- `fwdSurvivor_density_le_of_finite` (C2), `infinitelyManyOrbits_of_fwdSurvivor_density` (C2′),
  `infinitelyManyOrbits_of_bwdSurvivor_density` (C2′ mirror) all depend only on
  `[propext, Classical.choice, Quot.sound]`.
- `private` on `tendsto_fwdWindowSurvivor_density` was not touched.

## How

Helpers in `CollatzMoonshot/AmusicalSurvivorCeiling/Packing.lean`, namespace
`CollatzMoonshot.Amusical.Ceiling`, written once for a generic pair `f, g : ℤ → ℤ` with
`f ∘ g = id`, a Lemma-K bound for `g`, an orbit bridge, and "`f`-survivor ∧ `g`-window ⇒
`IsWindowMin`".  The forward targets use `(f, g) = (U, V)`; the backward mirror uses `(V, U)`
(Lemma K's `.1` half, `Or.symm` on the bridge).  So kickoff item 11 (the mirror) cost no extra
lemmas.

- `le_iterate_of_firstDrop` (P′), `le_four_pow_mul_sub` (gap, via `Nat.find` on the first drop).
- `card_le_of_sep` (packing: map `n ↦ n / D` into `range (X/D + 1)`).
- `card_orbit_le`: one orbit, `[X/M, X)`, `≤ 8 M 4^L + 1`.  Uses `4·4^L ≤ X/M` (not `2·4^L` as in
  the kickoff) so that `X/D ≤ 8 M 4^L` holds with the floors.
- `exists_iterate_of_mem_amusicalOrbit`, `card_le_of_finite` (`Finset.card_le_mul_card_image`
  over the orbit map), `card_survivor_le_split`, `density_le_of_finite`,
  `infinitelyManyOrbits_of_density`.

## Next steps

Nothing is owed on this kickoff.  The host merges `wip/amusical-ceiling`.
