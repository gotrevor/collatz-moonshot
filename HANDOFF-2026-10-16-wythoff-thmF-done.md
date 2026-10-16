# HANDOFF 2026-10-16 — Wythoff quadratic Theorem F: done

Branch `wip/wythoff-thmF`, HEAD `3ab8e79` (plus this doc).  Not pushed (box has no egress).

## Done

`CollatzMoonshot/WythoffQuadratic.lean` (kickoff `KICKOFF-2026-10-16-wythoff-thmF.md`) is
sorry-free: all 51 ratified statements proved for `α = 2r + 2√(r² − r)`, `r ≥ 2`.  Headline
`#print axioms`: `propext, Classical.choice, Quot.sound`.  Ratified statement texts checked
unchanged against `04d9e26`.  `SflOddDensityHalf` remains a hypothesis of the two density
theorems, as ratified.  Details and proof architecture: `HANDOFF-wythoff-thmF.md`.

Two ratified theorems were moved (statements unchanged) below the counting lemmas they use:
`wqPerm_infinitelyManyInfiniteOrbits`, `wqpPerm_infinitelyManyInfiniteOrbits`.

## Next steps (host)

1. Push `wip/wythoff-thmF` and open a PR to `main`.
2. Optional follow-ups, not in scope: the `O(log X)` error term (Ostrowski) and an
   unconditional density would need equidistribution of `k√m` mod 1 (not in Mathlib).
