# HANDOFF amusical t1arith (2026-10-14)

All five ratified targets in `CollatzMoonshot/AmusicalExcursionCode.lean` are proved:
`eq_amusical_of_branch`, `eq_amusical_of_forall_branch` (Theorem LOC), `defect_mod_delta`
(Theorem R), `gcd_offset_eq_gcd_defect` (Theorem DIV), `amusical_iterate_ge_iff_offset`.
`#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.  Full `lake build` green.

Proof notes:
- LOC.1: `unfold amusical; split_ifs <;> omega`.
- R: `Int.modEq_iff_dvd.2 ⟨-p, by linear_combination -h⟩`.
- DIV: `C = 2^a d + Δ(-p)`, `Int.gcd_add_mul_left_left`, then `Δ` odd gives
  `IsCoprime (2^a) Δ` (explicit Bezout from `Δ = 2k+1`), cancelled via natAbs and
  `Nat.Coprime.gcd_mul_left_cancel`.
- Ordering: `nlinarith` with `0 < 2^a`.

Nothing open in this file.  Sorries in the stacked reglue / ncentropy files belong to other
treadmills and were not touched.
