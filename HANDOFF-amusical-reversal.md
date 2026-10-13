# Handoff: amusical reversal (Lane R)

## 2026-10-13 lap

The scoped target remains the three `sorry`s in
`CollatzMoonshot/AmusicalReversal.lean`.  No ratified declaration was changed.

Concrete crux reduction: `orbit_inter_fixedPoints_ncard_le_two` is the first
load-bearing leaf.  After applying `reversing_zpow_fixed` relative to any fixed
orbit point, every other fixed point is a 2-torsion class in the cyclic orbit
`ℤ / {k | (σ^k) x = x}`.  Thus the remaining formal core is the standard fact
that a cyclic group has at most two solutions of `2 • q = 0`; the infinite
orbit case has one and a finite orbit identifies the two possible residue
classes `0` and `p/2`.  Direct searches found the useful orbit/ZMod machinery
in `Mathlib/Data/ZMod/QuotientGroup.lean`, notably the orbit equivalence at
lines 108--110, but no ready-made cardinality lemma for this 2-torsion set.

One bounded Aristotle job is in flight, with no other job concurrently active:

```text
project 68ee79c1-57d5-4a35-83bb-77f20f5af53d
task    3f90e42f-392d-42e2-ac48-89bf0ed17540
target  orbit_inter_fixedPoints_ncard_le_two
```

Next attack: harvest that job, kernel-check it against this repository, and if
it is partial, finish its cyclic 2-torsion leaf using either the orbit-to-ZMod
equivalence or a least-positive-period split.  Then use the proved ncard bound
for the easy `←` direction of `infinitelyManyOrbits_iff_reversor`; its `→`
direction still needs the orbit-base reflection construction.  Theorem NR is
the final and largest obligation.

Verification for this checkpoint: run
`~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-reversal --target CollatzMoonshot.AmusicalReversal`.
