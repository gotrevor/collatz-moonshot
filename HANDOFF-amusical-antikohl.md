# HANDOFF: amusical anti-Kohl

## 2026-10-14: Theorem T orbit trichotomy isolated

The order-theoretic crux of `orbit_densityZero_of_transientCone` is now explicit in three proved
helpers in `CollatzMoonshot/AmusicalAntiKohl.lean`:

* `cone_mem_zpow_mono`: forward invariance makes membership monotone in the integer coordinate of
  a two-sided permutation orbit;
* `exists_first_of_monotone_int`: a nonempty, non-universal monotone predicate on `ℤ` has a first
  true index;
* `cone_orbit_trichotomy`: every orbit is wholly inside the cone, wholly outside it, or has a
  first cone point.

This removes the main qualitative ambiguity in the paper proof.  In the transition case with
first index `t`, a point at coordinate `k ≥ t + n` lies in `(σ ^ n) '' S`, while a point at
coordinate `k < t - n` lies in the `n`-step never-entering set.  Thus only the finite coordinate
interval around `t` remains to be converted into the filtered-box cardinality estimate.

Verification attempted:

```text
git diff --check
lake env lean -j1 CollatzMoonshot/AmusicalAntiKohl.lean
```

`git diff --check` passes.  The first Lean run reached elaboration, exposed an unavailable helper
name (`Int.exists_eq_add_of_le`), and the proof was rewritten using `Int.toNat`.  Three subsequent
checks then failed during imports with the environment's intermittent `Too many open files`
failure.  A later retry completed successfully with exactly the five pre-existing target sorry
warnings.

Current blocker: no mathematical or operator blocker.  Five ratified target sorries remain.  The
only immediate issue is the transient import-level file-descriptor failure.

Next highest-value attack: prove that, for a finite seed set `F`, the part of its orbit union
outside the two `n`-cores has
cardinality at most `F.card * (2 * n + 1)`.  Combine that fixed finite error with the two
`IntDensityLE` bounds (epsilon split in half) to close `orbit_densityZero_of_transientCone`.

## 2026-10-14: five ratified targets proved

`CollatzMoonshot/AmusicalAntiKohl.lean` now has five sorries rather than ten.  This checkpoint
closes the two explicit class witnesses, the anti-Kohl implication for a seventh orbit, the
finite-control bijection, and the mixed-prime counterexample:

* `amusical_antiKohl_class`: use modulus `4`, numerator `3`, denominators `2` and `4`, and
  intercepts `0`, `1`, and `-1`; the RCWA equations are Presburger arithmetic and the two
  slopes have `3`-adic valuation one.
* `kappa_antiKohl_class`: use modulus `6`, numerator `2`, denominators `1` and `3`, and the six
  displayed intercepts from the definition of `kappa`; the slopes have `2`-adic valuation one.
* `atLeastSevenOrbits_of_antiKohl`: anti-Kohl rules out a tail in the orbit of `8`.  A finite
  nonnegative complement would be bounded above and hence produce a modulus-one tail, so the
  complement is infinite.  Remove the finite known-cycle set, choose a new nonnegative `n`, and
  combine it with `{0, 1, 2, 4, 44, 8}` using the existing six-orbit separation theorem.
* `hFive_bijective`: an explicit inverse sends residues `0, 2, 4 mod 5` to the three even input
  classes and residues `1, 3 mod 5` to the two odd input classes.  Both inverse identities are
  checked by residue arithmetic.
* `mixedPrime_single_orbit`: write the conjugating equivalence as `e` and its explicit inverse as
  `g`.  On each of the `30` input classes, the conjugate is affine with slope `3/2` when `g r` is
  even and `2/3` otherwise.  In `e`-coordinates it is translation by one, so choosing
  `n = e.symm y - e.symm x` proves that every two integers are on the same orbit.

The mixed-prime residue calculation needs `maxHeartbeats 1000000`; it is a finite kernel-checked
`interval_cases`/`omega` proof, not a decision-procedure axiom.  Ratified declarations and
definitions are unchanged.  No new axiom or `native_decide` was introduced.

Verification run:

```text
git diff --check
lake env lean -j1 CollatzMoonshot/AmusicalAntiKohl.lean
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-antikohl \
  --target CollatzMoonshot.AmusicalAntiKohl
```

The direct check succeeds with exactly the five remaining sorry warnings.  The real target gate
is FORMALIZE-tier green (8710 jobs).  Two earlier gate attempts hit the environment's intermittent
`Too many open files` import failure; an unchanged retry completed successfully.

Current blocker: five ratified targets remain:

* `orbit_densityZero_of_transientCone` and `infinitelyManyOrbits_of_transientCone`;
* the route-decisive residue-connectivity gate `amusical_no_periodic_cone`;
* the two explicit core estimates `kappa_orbit_densityZero` and
  `sigmaTau_orbit_densityZero`.

There is no external blocker.  A bounded Aristotle submission for
`amusical_no_periodic_cone` could not be started because another global Aristotle job was already
running; no job from this worktree is in flight.  Corpus and sibling-worktree searches found no
existing proof of the gate or Theorem T.  Finite computation through modulus `200` is evidence
only and was not used as a proof.

Next highest-value attack: prove `orbit_densityZero_of_transientCone`.  First isolate the orbit
trichotomy under forward closure of `S`: after deleting at most `2n` points per seed, each orbit
lies in `(σ ^ n) '' S` or in `{x | ∀ j ≤ n, (σ ^ j) x ∉ S}`.  Turn that inclusion into
a filtered box-cardinality estimate for a finite seed set, then use both `IntDensityLE`
hypotheses with epsilon split in half.  This closes the reusable engine before formalizing
the positive-density contradictions in `infinitelyManyOrbits_of_transientCone`.
