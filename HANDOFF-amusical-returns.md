# HANDOFF: amusical returns treadmill

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
