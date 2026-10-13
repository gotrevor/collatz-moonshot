# HANDOFF: seventh orbit formalization

## 2026-10-13 lap: cofinite reformulation closed

### Concrete advance

- Proved `atLeastSeven_of_orbit8_not_cofinite` without changing its ratified statement.
- The proof removes the finite `knownCycleMembers` set from the assumed infinite complement of
  `amusicalOrbit 8`, chooses a nonnegative witness `n`, and builds the seven representatives
  `{n, 0, 1, 2, 4, 44, 8}`.
- Separation from the five known finite cycles uses `amusicalOrbit_subset_of_closed`; separation
  from the orbit of `8` uses the witness's membership in the assumed set difference; separation
  among the original six representatives uses `amusical_six_distinct_orbits`.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh.lean` (green; warnings only for the three
  remaining ratified target sorries).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms
  CollatzMoonshot.Amusical.atLeastSeven_of_orbit8_not_cofinite` (8710 jobs,
  `FORMALIZE-TIER GREEN`).  The proved theorem uses exactly `Classical.choice`, `Quot.sound`, and
  `propext`; the gate reports only the three remaining target sorries.

### Current blocker

Three independent targets remain: `sparse_sweep`, `amusical_pow_classUnion_invariant`, and
`rewire_single_orbit`.  There is no external blocker.  Each needs substantial new infrastructure;
the first proof was intentionally closed before opening one of those larger constructions.

### Next highest-value attack

Attack `rewire_single_orbit` next, as directed by the kickoff.  First isolate reusable lemmas that
an infinite orbit of a permutation of `ℕ` visits every bounded interval only finitely often and
therefore crosses each sufficiently high dyadic annulus in both time directions.  Then formalize a
sparse family of cuts before constructing the rewired permutation.  Keep all helpers in
`CollatzMoonshot/AmusicalSeventh/` and leave the four ratified statements unchanged.
