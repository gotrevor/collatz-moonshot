# HANDOFF 2026-10-17: wythoff-classify done

Branch `wip/wythoff-mirrorY`; HEAD `21e11e0` (+ this handoff commit).  Kickoff:
`KICKOFF-2026-10-16-wythoff-classify.md`; running notes: `HANDOFF-wythoff-classify.md`.

## Done

All 46 kickoff statements proved; the three files are sorry-free.

| file | headline | axioms |
|---|---|---|
| `WythoffAutomaton.lean` | Theorem N (`first_step_odd_iff`, …), Theorem O (`thmO_iff`) | propext, choice, Quot.sound |
| `WythoffSeven.lean` | `minimalPeriod_alphaP_twenty`, `infinite_minimalPeriod_seven` (unconditional) | same |
| `WythoffMirrorY.lean` | Y′ classification, count, `ymPerm_infinitelyManyInfiniteOrbits`, `tendsto_minCount_ymPerm` (conditional on `WeylEquidistributionMulti` only) | same |

This lap: the Y′ density, via the new general conjugacy `wy_mirror_eq_neg`
(`W_β(n) = −W_α(−n − 1) − 1` for every `α > 1`, `β = α/(α − 1)`), which transfers Theorem Y's
cylinders, Weyl input (frequencies negated) and sandwich to the mirror; no new polygon work.

`box done --green` issued; scope `sorry-free:` on the three files is met.

## Next (for a future, operator-chosen lap)

* `DIRECTION.md` CURRENT DIRECTIVE still says no new proof lap without a new idea; obey it.
* Candidate: re-derive `WythoffLine`'s mirror density from the main side via
  `wy_mirror_eq_neg` (simplification, not new mathematics).
* The kickoff's out-of-scope layer: Theorem A, Theorem Q's unboundedness half, the zonotope
  criterion, Proposition F, the "runs never reach length `d`" reading of Theorem O, the 7-cycle
  cylinder density (`≈ 0.09427` of evens).

Build: `lake build CollatzMoonshot.WythoffAutomaton CollatzMoonshot.WythoffMirrorY
CollatzMoonshot.WythoffSeven`.
