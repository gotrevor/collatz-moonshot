# HANDOFF 2026-10-15: amusical-zcore done

Branch `wip/amusical-zcore`, HEAD `408a6ea` (plus this doc).

## Done
* `CollatzMoonshot/AmusicalPeriodicInvariant.lean`: both ratified targets proved,
  `periodic_invariant_const` and `periodic_eventually_invariant_const`; `#print axioms`
  shows `propext, Classical.choice, Quot.sound` only.  Helpers: `periodic_int_mul`,
  `periodic_eq_mod`.  Statements unchanged; no `native_decide`; lines ≤ 100 chars.
* `box done` acknowledged: scoped target `sorry-free:CollatzMoonshot/AmusicalPeriodicInvariant.lean`
  is clean.  Details in `HANDOFF-amusical-zcore.md`.

## Next steps
* Host: push `wip/amusical-zcore` and merge.
* Downstream: Theorem Z (research §48) can now cite these two theorems for the
  column/row-mass constancy step.
