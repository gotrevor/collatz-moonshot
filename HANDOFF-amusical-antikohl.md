# HANDOFF: amusical anti-Kohl

## 2026-10-14: sigma-tau forward core algebra isolated

The easy half of the `sigmaTau_orbit_densityZero` automaton is now reduced to pure counting.
Three kernel-checked helpers establish that `S = {x | x % 4 = 2}` is a forward-invariant cone,
that `(sigmaTauPerm ^ n) x = 3^n * x` on `S`, and that the full forward core is exactly
`{3^n * x | x % 4 = 2}`.  In particular, no further dynamics remain in the forward estimate;
the next step is only the symmetric-box cardinality bound for this single dilated class.

Verification run:

```text
lake env lean -j1 CollatzMoonshot/AmusicalAntiKohl.lean
```

The direct check succeeds with exactly the three pre-existing target sorry warnings.  Two
earlier unchanged retries hit the environment's intermittent import-level `Too many open files`
failure.  No target statement, axiom, or decision certificate changed.

Current blocker: no external blocker.  The three ratified target sorries remain
`amusical_no_periodic_cone`, `kappa_orbit_densityZero`, and `sigmaTau_orbit_densityZero`.
For the last, the forward core is now explicit; the load-bearing missing part is still the
13-type backward survivor recursion with decay `(1/2)(3/4)^(n-1)`.

Next highest-value attack: prove a reusable `IntDensityLE` bound for a single dilated residue
class and discharge the forward hypothesis of Theorem T from `sigmaTau_forward_core`.  Then
encode the 13 backward survivor types as finite residue sets and prove their one-step cardinality
recursion, aiming only for the geometric upper bound required by Theorem T.

## 2026-10-14: Theorem T and its orbit consequences proved

The reflection audit found no statement mismatch: the scoped gate is exactly the remaining
`sorry`s in `CollatzMoonshot/AmusicalAntiKohl.lean`, `AntiKohlConjecture` remains an open
definition, and the transient-cone route is semantically sufficient.  The missing abstraction
was simultaneous depth control plus a stable filtered-box count, not a stronger density notion.

`orbit_densityZero_of_transientCone` is now kernel-checked.  The proof chooses forward and
backward depths for `ε/4`, advances both to their sum using cone antitonicity, combines the
per-orbit exceptional intervals into one `Finset`, and absorbs its fixed cardinality with
`tendsto_const_div_atTop_nhds_zero_nat`.  A private `intBoxCount` fixes the classical decision
procedure used by repeated `Finset.filter` expressions; without that shared definition,
extensionally equal predicates produced non-definitionally-equal filtered finsets.

`infinitelyManyOrbits_of_transientCone` is also proved.  The new helper
`not_intDensityZero_of_containsClassTail` injects `t` consecutive points of a residue-class tail
into a symmetric box of radius at most `2Mt`, giving a fixed positive density lower bound.  If
there were finitely many orbits, choosing one representative from each would make a finite orbit
union equal to `Set.univ`, contradicting Theorem T.  Applying the same obstruction to a singleton
seed rules out a class tail in every orbit.

Verification run:

```text
lake env lean -j1 CollatzMoonshot/AmusicalAntiKohl.lean
git diff --check
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-antikohl \
  --target CollatzMoonshot.AmusicalAntiKohl \
  --axioms CollatzMoonshot.Amusical.orbit_densityZero_of_transientCone
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-antikohl \
  --target CollatzMoonshot.AmusicalAntiKohl \
  --axioms CollatzMoonshot.Amusical.infinitelyManyOrbits_of_transientCone
```

The direct check succeeds with exactly the three remaining target sorry warnings.  No new axiom,
`native_decide`, or target-statement change was introduced.  Both 8710-job scoped gates are
FORMALIZE-tier green.  Each new headline theorem's axiom ledger is exactly `Classical.choice`,
`Quot.sound`, and `propext`.

Current blocker: no external blocker.  Three ratified target sorries remain:
`amusical_no_periodic_cone`, `kappa_orbit_densityZero`, and
`sigmaTau_orbit_densityZero`.  These are precisely the residue-connectivity gate and the two
periodic-core automata identified by the kickoff; the reusable transient-cone engine is complete.

Next highest-value attack: isolate periodic-set counting infrastructure for
`sigmaTau_orbit_densityZero`, starting with the easy forward core
`(sigmaTauPerm ^ n) '' {x | x % 4 = 2} = {x | x % (4 * 3^n) = 2 * 3^n}` and its density bound.
Then encode the backward survivor recursion as finite residue classes, aiming only for the
geometric upper bound `(1/2)(3/4)^(n-1)`.  This is a smaller, more checkable first automaton than
the four-type spectral recursion needed for the `kappa` forward core.

## 2026-10-14: finite-exception bridge for Theorem T proved

The missing geometric step after the orbit trichotomy is now kernel-checked as
`exists_orbit_exception`.  For every seed `x` and depth `n`, it constructs an explicit finite set
`E` of at most `2n + 1` orbit points such that the full two-sided orbit is contained in the union
of the forward core `(σ ^ n) '' S`, the `n`-step never-entering set, and `E`.

In the transition case, `E` is the image of the coordinate interval
`[t-n, t+n]`.  Coordinates below it remain outside `S` for the next `n` iterates, by contraposing
cone monotonicity against the last false coordinate `t-1`; coordinates above it are images under
`σ^n` of cone points.  The wholly-inside and wholly-outside cases have empty exceptions.  This is
the load-bearing set inclusion promised by the previous handoff; no new axiom, decision
certificate, or target statement change was introduced.

Verification run:

```text
lake env lean -j1 CollatzMoonshot/AmusicalAntiKohl.lean
git diff --check
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-antikohl \
  --target CollatzMoonshot.AmusicalAntiKohl
```

The direct check succeeds with exactly the five pre-existing target sorry warnings.  The real
target gate is FORMALIZE-tier green (8710 jobs).

Current blocker: no external blocker.  Five ratified target sorries remain.  For Theorem T, only
the finite-union cardinality and epsilon/Tendsto bookkeeping remains after the proved cover.

Next highest-value attack: for a finite seed set `F`, union the exception sets from
`exists_orbit_exception` and bound their cardinality by `F.card * (2*n+1)`.  Filter the resulting
set inclusion by `Icc (-X) X`, use the two `IntDensityLE` bounds with epsilon split in half, and
absorb the fixed exception cardinality for large `X`.  This should close
`orbit_densityZero_of_transientCone`, after which prove the positive density of a residue-class
tail to close `infinitelyManyOrbits_of_transientCone`.

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
