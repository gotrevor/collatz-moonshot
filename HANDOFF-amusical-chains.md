# HANDOFF — amusical chains

## 2026-10-13 treadmill lap: survival invariant formalized

Concrete advance:

- Added exact finite-horizon rational-state walks `fwdWalk` and `bwdWalk` in
  `AmusicalChains.lean`.
- Proved the shared load-bearing estimates `fwdWalk_ge` and `bwdWalk_ge`:
  whenever `0 < a < b`, survival for every remaining horizon is at least
  `1 - a/b`.  The proofs are by induction and kernel-check both cases from the
  kickoff: when both children survive their weighted exponential deficits
  average exactly to the parent deficit; when the downward child crosses the
  boundary, its failed inequality supplies precisely the missing estimate.
- This isolates the remaining work for `fwdSurv_ge` and `bwdSurv_ge` to a
  semantic bridge between the existing `Fin L → Bool` word sums and the new
  head-recursive walks.  No statement was changed, and no axiom or native
  certificate was added.

Verification in this lap:

- `lake env lean CollatzMoonshot/AmusicalChains.lean` passed, reporting only
  the same three disclosed target sorries.
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-chains
  --target CollatzMoonshot.AmusicalChains` passed (see commit checkpoint).

Current blocker / next highest-value attack:

1. Define generalized semantic word sums whose current rational height is
   `a/b`, split them on the *first* Boolean letter using `Fin.cases` (or prove a
   head analogue of `sum_bool_snoc`), and prove by induction that they equal
   `fwdWalk` / `bwdWalk`.  Specializing the forced first upward step gives
   `fwdSurv (L+1) = (1/2) * fwdWalk L 2 3` and
   `bwdSurv (L+1) = (2/3) * bwdWalk L 3 4`; the new lemmas then yield `1/6`.
   Handle `L=0` directly.  This should close both survival targets together.
2. Then attack `exists_sublinearlyRecurrent_of_finitelyManyOrbits` using the
   counting route already described below.

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
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-chains
  --target CollatzMoonshot.AmusicalChains`: **FORMALIZE-TIER GREEN**, 8710 jobs;
  it reports precisely the three remaining `sorry` declarations at source
  lines 40, 44, and 59.

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
