# HANDOFF — Wythoff quadratic Theorem F (`CollatzMoonshot/WythoffQuadratic.lean`)

Kickoff: `KICKOFF-2026-10-16-wythoff-thmF.md`.  Branch `wip/wythoff-thmF`.

## Status (2026-10-16)

Proved: §1 (bridges), §2 (bijectivity, positivity), §3 (Theorem D, partner D, step bounds),
§4 (Theorem F classification for `W`), §5 exact count `minCount_add_countB`, `minCount_ge`,
`minCount_le`, and `wqPerm_infinitelyManyInfiniteOrbits`.

Open: `tendsto_minCount` (density, conditional on `SflOddDensityHalf`), and all of §6 (partner).

## Decisions

- **Integer/real route.**  Everything goes through `sfl_bounds : sfl ≤ 2k√m < sfl + 1`
  (strict on the left for `k ≠ 0` by irrationality, `sfl_lt`) and `sfl_eq_of` (pin `sfl` by
  real bounds).  Theorem D is the identity `2j√m − T = (r − √m)(2k√m − s − 1) + 1`
  (`linear_combination` with `√m² = m`), then `nlinarith`.
- **Abstract skeleton** (`Skel σ E`, section `Skeleton`): `pos`/`up`/`twoStep`/`down`.  The
  minimum of an orbit of a non-fixed `x > 0` is an entry (`Skel.entry_of_min`); an entry is the
  strict minimum (`Skel.entry_lt`, via `Skel.after` forward and `Skel.before` backward);
  injectivity of `t ↦ σ^t x` from the entry's strict climb; both escapes from "injective +
  positive ⇒ tends to ∞" (`tendsto_atTop_of_injective_pos`).  No quantitative growth needed.
  `W` instance: `wq_skel` (E = evens).  Partner: instantiate with E = odds.
- **Moved** `wqPerm_infinitelyManyInfiniteOrbits` (statement unchanged) to after `minCount_le`
  because it uses `minCount_ge`.  Plan the same for `wqpPerm_infinitelyManyInfiniteOrbits`
  (needs a helper lower bound `minCountP_ge`).
- Host flake: the pre-commit hook's build sometimes dies with "Too many open files" (host
  bind mount).  Confirm green with a direct `lake build CollatzMoonshot.WythoffQuadratic`,
  then commit with `--no-verify` and say so in the message.

## Next

1. §6 partner: `wqp_skel` (E = odds; `up` = `wqp_bounds`.2.2, `twoStep` = `wqp_wqp_of_even`,
   `down` = `wqp_bounds`.2.1), `isEntryP_iff` mirror, count `minCountP_add_countBP` mirror.
2. Density `tendsto_minCount`, `tendsto_minCountP`.

Scratch tool: `tmp/thmF/fill.py <patch.py>` replaces `  sorry` bodies by name and inserts
helpers before a named theorem.
