# HANDOFF 2026-10-14: amusical t1arith done

Branch `wip/amusical-t1arith`; proofs landed in `351e9de`.

## Done

The scoped target `sorry-free:CollatzMoonshot/AmusicalExcursionCode.lean` is met.  All five
ratified statements are proved, unchanged:
- `eq_amusical_of_branch`, `eq_amusical_of_forall_branch` (Theorem LOC): exactly one of `3x/2`,
  `(3x ± 1)/4` is an integer, namely `U x`; so a map built from `U`'s branches is `U`.
- `defect_mod_delta` (Theorem R): `2^a (U^g p − p) ≡ C (mod 3^g − 2^a)`.
- `gcd_offset_eq_gcd_defect` (Theorem DIV): `gcd(C, Δ) = gcd(U^g p − p, Δ)` for `a ≥ 1`.
- `amusical_iterate_ge_iff_offset`: `U^g p ≥ p` iff `Δ p + C ≥ 0`.

`#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.  Full `lake build` is
green.  The proof notes are in `HANDOFF-amusical-t1arith.md`.

## Next

Nothing is open in this scope.  The sorries in the stacked reglue / ncentropy files belong to
other treadmills and are designated-open.  `DIRECTION.md` CURRENT DIRECTIVE (awaiting a new idea)
stands, so no follow-on lap is implied.
