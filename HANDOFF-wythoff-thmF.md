# HANDOFF — Wythoff quadratic Theorem F (`CollatzMoonshot/WythoffQuadratic.lean`)

Kickoff: `KICKOFF-2026-10-16-wythoff-thmF.md`.  Branch `wip/wythoff-thmF`.

## Status (2026-10-16) — COMPLETE

`CollatzMoonshot/WythoffQuadratic.lean` is sorry-free; all 51 ratified statements proved.
`#print axioms` on the headlines: `propext, Classical.choice, Quot.sound` only.  The ratified
statement texts were checked unchanged against `04d9e26` (script diff of every declaration
header and every ratified `def`).  `SflOddDensityHalf` stays a hypothesis of the two density
theorems, as ratified.

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

## Structure of the remaining proofs

- Density: `countA = oddCount(⌊(X + 1)/β⌋)` exactly (`W(2j − 1) ≤ X ⇔ jβ ≤ X + 1`, ceiling
  form), `countB = oddCount(⌊X/2r⌋)`; partner `countAP = evenCount(⌊(X + 1)/β⌋)`,
  `countBP = evenCount(⌊(X + 1)/2r⌋)`.  Generic `tendsto_ratio_of_bounds` (squeeze) and
  `tendsto_comp_ratio` (density along a linearly growing count); `density_value` closes the
  constant via `1/β = (2r + 2√m)/(4r)`.
- Both `…_infinitelyManyInfiniteOrbits` were moved (statements unchanged) below the counting
  lemmas they use; the partner one uses the unratified helper bounds `countAP_ge`,
  `countBP_le`.

Scratch tool: `tmp/thmF/fill.py <patch.py>` replaces `  sorry` bodies by name and inserts
helpers before a named theorem.
