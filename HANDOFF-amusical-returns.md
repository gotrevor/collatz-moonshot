# HANDOFF: amusical returns treadmill

## 2026-10-13: exits equal strict minima proved

`exits_eq_strictMinima` is now proved with its ratified statement unchanged.  The forward map sends
an exit to `orbitMinNat`; positivity and exit aperiodicity make that point the strict two-sided
minimum.  Conversely, `finite_forward_visits_below` supplies a finite nonempty set of visits below
`X`, whose maximum is the unique last visit and hence an exit.  The proof checks both inverse
directions through orbit equality; periodic orbits contribute to neither side without any
divergence assumption.

Verification:

- `lake env lean CollatzMoonshot/AmusicalReturns.lean` passes; its only warnings for proof debt are
  the two remaining target sorries.
- `~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-returns --target
  CollatzMoonshot.AmusicalReturns --axioms CollatzMoonshot.Amusical.exits_eq_strictMinima` passed:
  8710 jobs, `FORMALIZE-TIER GREEN`; the theorem's axiom ledger is exactly
  `[propext, Classical.choice, Quot.sound]`, and proof debt is at lines 196 and 424.
- `git diff --check` passes.

Current blocker: `exists_large_nonOrbitMin` and `return_defect_bound` remain independent hard proof
obligations.  This is mathematical/formalization work, not an operator blocker.

Next highest-value attack: `return_defect_bound`, the more uncertain analytic obligation.  First
factor one `amusical` step into its exact positive real multiplier and telescope the logarithms;
then isolate the distinct-iterate reciprocal sum before proving the stated logarithmic bound.

## 2026-10-13: exits/minima finiteness layer proved

The route-decisive infrastructure for `exits_eq_strictMinima` is now proved in
`CollatzMoonshot/AmusicalReturns.lean`.  Positive integers stay positive under every integer
power of `amusicalPerm`; an orbit parametrization by `ℤ` is injective exactly when the base
point has no nonzero return; the exit predicate implies this injectivity; and the strict-minimum
predicate implies both injectivity and finiteness of the set of forward times whose values lie
below a fixed cutoff.  In particular, the paper proof's “last forward visit” now has a finite,
nonempty set from which it can be selected without assuming orbit divergence.

Verification:

- `lake env lean CollatzMoonshot/AmusicalReturns.lean` passes; its only warnings are the three
  pre-existing target sorries.
- `~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-returns --target
  CollatzMoonshot.AmusicalReturns` passed: 8710 jobs, `FORMALIZE-TIER GREEN`; proof debt is exactly
  the three target sorries at lines 122, 129, and 259.
- `git diff --check` passes.

Current blocker: `exits_eq_strictMinima` still needs the explicit finite-set maximum construction
and the two inverse maps (exit to least natural orbit member, strict minimum to last forward
visit).  The mathematical finiteness and uniqueness inputs for that construction are now closed.

Next highest-value attack: define the maximum of `finite_forward_visits_below` (the set contains
time `0` for a strict minimum in `Icc 1 X`), prove its iterate is an exit, and use
`orbitMinNat` for the inverse map in `Finset.card_bij`.

## 2026-10-13: dense linear returns proved

`exists_denseLinearReturns_of_finitelyManyOrbits` in
`CollatzMoonshot/AmusicalReturns.lean` is now proved with its ratified statement unchanged.
The proof refines `exists_linearlyRecurrent_of_finitelyManyOrbits`: failure of zero density
supplies frequently many orbit points below `X`; chosen times are injective, and removing the
integer interval `(-ceil (εX/4), ceil (εX/4))` discards at most `2 ceil (εX/4)-1`
times.  The survivors therefore have cardinality at least `εX/2-1` and satisfy the pinned
absolute-time and value bounds.

Verification:

- `lake env lean CollatzMoonshot/AmusicalReturns.lean` passes; its only warnings are the three
  remaining target sorries.
- `~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-returns --target CollatzMoonshot.AmusicalReturns`
  passed: 8710 jobs, `FORMALIZE-TIER GREEN`; the only proof debt reported is the three remaining
  target sorries at lines 32, 39, and 169.
- Axiom audit for `CollatzMoonshot.Amusical.exists_denseLinearReturns_of_finitelyManyOrbits`
  reports exactly `[propext, Classical.choice, Quot.sound]`.

Current blocker: three independent statements remain: `exists_large_nonOrbitMin`,
`exits_eq_strictMinima`, and `return_defect_bound`.  This is hard-but-doable proof work, not an
operator blocker.

Next highest-value attack: prove `exits_eq_strictMinima`.  Package the positive orbit of each
`n ∈ [1,X]` by its least natural member (`orbitMinNat`) and use the unique last visit below `X`
on infinite orbits; periodic orbits contribute to neither filtered finset.
