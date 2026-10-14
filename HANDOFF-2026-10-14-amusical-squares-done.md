# HANDOFF 2026-10-14: amusical squares done

Branch `wip/amusical-squares`; proofs landed in `9461c52`, `495db6b`, `4fc930d`.

## Done

The scoped target `sorry-free:CollatzMoonshot/AmusicalSquares.lean` is met.  All four ratified
statements are proved, unchanged:
- `amusicalInv_iterate_cylinder`: `V^k` maps `3^k n + r` to `2^a n + s`, `k ≤ a ≤ 2k`,
  `0 ≤ s < 2^a`.
- `invariant_kernel_three_pow`: the `3^{mk}`-kernel of a `U^m`-invariant colouring lies in its
  `2`-kernel.
- `prefixRoot_eq_iff` (SQG1): prefix roots coincide iff every branch between is `E`.
- `infinitelyManyOrbits_of_squareReturnConfinement`: SRC implies Klamkin (a).  Each orbit carries
  `O_C(log H)` of the squares `1², …, H²` (`card_small_square_times_le`), so finitely many orbits
  cannot cover them.

`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.  Full `lake build` green.
Proof notes in `HANDOFF-amusical-squares.md`.

## Next

Nothing open in this scope.  The live question is `SquareReturnConfinement` itself (open).
