# PENDING_WORK

## Status (2026-08-24)

- **Harmonic-dual obstruction project: COMPLETE** (this session's scoped task).
  `no_positive_harmonic_local_certificate` proved sorry-free, depth-uniform,
  axiom-clean (`[propext, Classical.choice, Quot.sound]` + 4 `native_decide`).
  See `FRONT-A-HARMONIC-DUAL.md` §Results/§8 and `HANDOFF-2026-08-24-0530.md`.
- `src/` is sorry-free; full `lake build` green (8746 jobs).

## The repo's real headline cruxes (open, deep — narrow, don't clear in one lap)

The Collatz headline `Conjecture ↔ NoDivergentOrbit ∧ NoNontrivialCycle`
(`Descent.lean`, `Conjecture.lean`) rests on two fronts, each behind cited
axioms:

### Front B — `NoNontrivialCycle ↔ FrontB` (`FrontB/Dictionary.lean`)
Arithmetic front; cited axioms in `Assumed/`:
- `eliahou_min_cycle_length`, `hercher_odd_members_bound` (`Assumed/Cycles.lean`)
  — Baker linear-forms + continued fraction of `log₂3` + large computation.
- `baker_bounded_difference`, `hercher_min_circuit_count` (`FrontB/Threads.lean`).
- `abc` (`Assumed/ABC.lean`), used by `length_bounded_of_abc_and_boundedDen`.
- **Narrowing path** (not one lap): formalize the elementary cycle→S-unit/linear-
  forms reduction, isolating Baker's theorem as the single narrow cited input;
  or discharge the finite `hercher_*` circuit-count computations. See
  `FRONT-B-ROUTES.md`.

### Front A — `NoDivergentOrbit`
Rigidity front; rests on `tao_2019_almost_bounded` (`Assumed/Tao2019.lean`) and
`furstenberg_topological_rigidity` (`Assumed/Furstenberg.lean`, flagged OPEN).
The barriered backward-tree ladder (2/3→3/4→4/5 rungs, all green) is the
constructive lane; the harmonic no-go proved this session shows the uniform
local-certificate ladder **cannot** reach `α=1`, so Route A2 does not close the
divergence front alone — redirect to A1/A3 itinerary-rigidity.

## Note for the next operator
The scoped harmonic project is finished. Picking up a Front A/B axiom-narrowing
task is a deliberate refocus (deep, multi-lap) that should be operator-directed
rather than started blind at a session boundary.
