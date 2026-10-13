# HANDOFF — amusical chains

## 2026-10-13 treadmill lap

Concrete advance:

- Proved `IsWindowMin.iterate_eq_of_isWindowMin`.  The second window-minimum
  inequality is transported through `amusicalInv_iterate_eq_perm_pow` and
  `amusical_iterate_eq_perm_pow`; the inverse and forward powers cancel, and
  antisymmetry finishes.
- Proved `atLeastSeven_or_orbitEight_infinite`.  Under finiteness of the orbit
  of `8`, choose a nonnegative integer outside the finite union of that orbit
  and `knownCycleMembers`.  Closure of the known-cycle finset and
  `amusical_six_distinct_orbits` show that adjoining it to
  `{0,1,2,4,44,8}` gives seven pairwise distinct nonnegative orbits.
- Commits: `51afe24`, `9b2c913`.

Remaining scoped obligations are exactly `fwdSurv_ge`, `bwdSurv_ge`, and
`exists_sublinearlyRecurrent_of_finitelyManyOrbits`.  No statements were
changed, and no axiom or native certificate was added.

Verification in this lap:

- `lake env lean CollatzMoonshot/AmusicalChains.lean` passed after both proofs,
  with only the three remaining disclosed `sorry` warnings.
- The pre-commit full `lake build` passed twice: 8842 jobs each time.
- Final real gate is recorded below after this handoff is committed.

Current blocker / next highest-value attack:

1. Prove the two survival estimates together.  `AmusicalBound.lean` already
   proves the semantic-word/lattice-DP equivalences
   `fwdSurv_mul_two` and `bwdSurv_mul_three`; it currently is a sibling import,
   so `AmusicalChains.lean` may import it without an import cycle.  Add a
   start-height lattice survival function and prove the invariant
   `g L (a,b) >= 1 - 2^b/3^a` by induction, splitting the down-step-crosses-zero
   case exactly as in the kickoff.  Specialize after the forced first up-step
   to obtain both `1/6` bounds.  Do not use `native_decide`.
2. Then adapt the finite-orbit counting skeleton from
   `exists_linearlyRecurrent_of_finitelyManyOrbits`.  Use
   `windowMinDensity L`, `windowDensity_ge L`, and the newly proved separation
   lemma.  Periodic window minima must be isolated as the finite exceptional
   set before converting separation of values into separation of orbit times.
   Pigeonhole first over the finitely many orbits for each large `L`, then over
   the orbit choice as `L` tends to infinity.

