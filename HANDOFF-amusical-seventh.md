# HANDOFF: seventh orbit formalization

## 2026-10-13 lap: two-primary residue transitivity closed

### Concrete advance

- Added `CollatzMoonshot/AmusicalSeventh/Residue.lean` and proved the full residue-transitivity
  theorem for every power-of-two modulus, `amusical_pow_classUnion_invariant_pow_two`.
- Proved generic image-equality infrastructure: equality of a set with its image under a
  permutation makes membership invariant under every multiple of the given iterate.
- Proved `exists_amusical_mul_iterate_modEq_pow_two`: after a time constrained to be a multiple
  of any positive `m`, a point in any prescribed class modulo `2^b` can land in any prescribed
  output class.  The proof uses the exact forward-cylinder formula; its slope `3^t` is a unit
  modulo `2^b`.
- No ratified statement changed, no axiom or `native_decide` was introduced, and no new `sorry`
  was added.  The two original targets remain open.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Residue.lean` (green).
- `lake env lean CollatzMoonshot/AmusicalSeventh.lean` (green; only the two original target
  sorry warnings).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms
  CollatzMoonshot.Amusical.amusical_pow_classUnion_invariant_pow_two` (`FORMALIZE-TIER GREEN`;
  axiom ledger exactly `Classical.choice`, `Quot.sound`, `propext`).
- `git diff --check` (clean).

### Current blocker

There is no external blocker.  For `amusical_pow_classUnion_invariant`, the `2`-primary factor is
now complete.  The symmetric backward-cylinder argument should close the `3`-primary factor.
The route-decisive remaining part is transitivity modulo the factor coprime to `6`, where branch
words must generate a translation in the finite affine group.  `sparse_sweep` remains untouched.

### Next highest-value attack

Prove `exists_amusical_mul_iterate_modEq_pow_three` from
`amusicalInv_iterate_add_pow_three_mul_slope`, then package the power-of-three class-union
corollary.  After that isolate a coprime-modulus affine-word translation lemma and combine the
three components by CRT to discharge the ratified theorem.

## 2026-10-13 lap: rewiring barrier closed

### Concrete advance

- Proved the ratified `rewire_single_orbit` statement without changing its type.  Two target
  sorries now remain in `CollatzMoonshot/AmusicalSeventh.lean`.
- The fresh review found that the paper's annular upper bounds are unnecessary for sparsity.
  `sparseCutPoint` enumerates every `(base point, requested time, direction)` and chooses the
  corresponding orbit cut above `(q+1)^2`.  The resulting `sparseOrbitCuts` meets both tails of
  every infinite orbit cofinally, contains only infinite-orbit points, and every decidable subset
  has density zero.
- `nextSparseCut` and `prevSparseCut` are inverse nearest-cut maps.  The finite segments between
  cuts are reconnected so their induced successor is a conjugate of translation by one on `ℤ`.
  This makes all original infinite-orbit points lie on one new orbit and leaves finite orbits
  untouched.
- The changed domain satisfies the explicit stronger bound
  `card {n < N | τ n ≠ σ n} ≤ Nat.sqrt (2*N+1)`, using only the forward half of the ratified
  doubling hypothesis.  Its real square-root majorant proves the required density limit.
- No new axiom and no `native_decide` were introduced.  The two ratified statements still open
  are `amusical_pow_classUnion_invariant` and `sparse_sweep`.

### Verification

- `lake env lean CollatzMoonshot/AmusicalSeventh/Rewire.lean` (green).
- `lake build CollatzMoonshot.AmusicalSeventh.Rewire` (8710 jobs, green).
- `lake env lean CollatzMoonshot/AmusicalSeventh.lean` (green; warnings only for the two remaining
  target sorries).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-seventh --target
  CollatzMoonshot.AmusicalSeventh --axioms CollatzMoonshot.Amusical.rewire_single_orbit`
  (8711 jobs, `FORMALIZE-TIER GREEN`; axiom ledger exactly `Classical.choice`, `Quot.sound`,
  `propext`).
- `git diff --check` (clean).  The ratified theorem statement is unchanged from kickoff commit
  `5fa5871`; only its proof body changed this lap.

### Current blocker

There is no external blocker.  `amusical_pow_classUnion_invariant` is now next by the ratified
order and requires a uniform strong-connectivity argument for the residue graph of every positive
power of `amusical`.  The existing cylinder transport module supplies exact forward and backward
congruence control but does not yet package the mixed `2`/`3`/coprime CRT reachability theorem.
`sparse_sweep` remains the final and heaviest target.

### Next highest-value attack

Attack `amusical_pow_classUnion_invariant`.  First state and prove a point-to-point residue
reachability lemma: for `0 < m,M` and residues `r,s : ZMod M`, choose integers `x ≡ r` and a
positive multiple `L` of `m` with `amusical^[L] x ≡ s`.  Reuse
`amusical_iterate_add_forwardPeriod_mul`, `amusical_iterate_modEq_two`, and
`amusicalInv_iterate_modEq_three`; isolate the modulus coprime to `6` before the final CRT.  Then
derive the target from forward/backward invariance of the class union.  Adversarially test the
reachability statement at small `m,M` before committing its exact quantifiers.

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
