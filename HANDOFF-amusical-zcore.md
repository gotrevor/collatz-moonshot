# HANDOFF: amusical-zcore (Theorem Z arithmetic core)

Status 2026-10-15: **done.**  Both targets in `CollatzMoonshot/AmusicalPeriodicInvariant.lean`
are proved; `#print axioms` shows only `propext, Classical.choice, Quot.sound`.

* `periodic_invariant_const`: level set `{f = f n}` is the class union of
  `R = {r : ZMod M | f r.val = f n}` (`periodic_eq_mod`), mapped onto itself by `U`
  (inverse via `amusicalInv`), so `amusical_pow_classUnion_invariant 1 M` forces `R = univ`.
* `periodic_eventually_invariant_const`: `n ↦ f (U n)` is `4M`-periodic by the existing
  `amusical_add_four_mul` (AmusicalWindow); shift by `j = N + |n|` copies of `4M` to leave
  the window, then reduce to the first theorem.
* Helpers added: `periodic_int_mul`, `periodic_eq_mod`.

Ratified statements unchanged.  No new axioms, no `native_decide`.
