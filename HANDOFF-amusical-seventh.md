# HANDOFF: seventh orbit formalization

## 2026-10-13 lap: rewiring properness and annulus crossing

### Concrete advance

- Added `CollatzMoonshot/AmusicalSeventh/Rewire.lean`, imported by the scoped target.
- Proved the generic kernel-checked lemma `perm_zpow_apply_injective_of_infinite`: the integer
  parametrization of any infinite permutation orbit is injective.
- Derived `finite_orbit_times_le` and `exists_nat_iterate_gt`: an infinite orbit visits every
  bounded subset at only finitely many integer times and is unbounded in both time directions.
- Proved `exists_forward_backward_mem_Ico`, the first quantitative load-bearing input to
  `rewire_single_orbit`: under the ratified doubling bound, every infinite orbit crosses
  `[Y, 2Y)` both forward and backward whenever its starting point is below `Y`.
- No ratified statement was changed. The three target sorries remain explicit.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Rewire.lean` (green; one non-finding style
  suggestion concerning a local `NeZero` instance).
- `lake build CollatzMoonshot.AmusicalSeventh.Rewire CollatzMoonshot.AmusicalSeventh` (8711 jobs,
  green; only the three expected target-sorry warnings and inherited publish-tier suggestions).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh` (8711 jobs, `FORMALIZE-TIER GREEN`; exactly the three expected
  target sorries remain).

### Current blocker

`rewire_single_orbit` still needs the global combinatorial construction. The analytic/properness
part is now closed. The remaining work is to enumerate infinite orbit classes, choose annular cuts
with a quantitative `O((log N)^2)` support bound, split the original bi-infinite lines into finite
segments, enumerate those segments by `ℤ`, and package the successor relation as an
`Equiv.Perm ℕ` while proving agreement on finite orbits and density zero.

### Next highest-value attack

Define the equivalence relation `a ~ b ↔ ∃ j : ℤ, (σ ^ j) a = b` on the infinite-orbit subtype and
obtain a countable transversal ordered by least natural representative. For orbit number `i`, use
`exists_forward_backward_mem_Ico` at scales `4^k`, `k ≥ i`, to select two cuts. First prove the
standalone counting lemma that these selected cut values have density zero; only then build and
verify the segment-splicing permutation.

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
