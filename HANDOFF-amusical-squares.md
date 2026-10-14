# HANDOFF amusical squares (2026-10-14)

All four ratified targets in `CollatzMoonshot/AmusicalSquares.lean` are proved, statements
unchanged: `infinitelyManyOrbits_of_squareReturnConfinement` (SRC ⇒ (a)), `prefixRoot_eq_iff`
(SQG1), `amusicalInv_iterate_cylinder` (canonical cylinder), `invariant_kernel_three_pow` (AUT
core).  `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.  Full `lake build`
green.  `SquareReturnConfinement` stays an open hypothesis `Prop`, used only as a hypothesis.

Helpers (`CollatzMoonshot/AmusicalSquares/`):
- `Cylinder.lean`: `amusicalInv_three_mul_add` (`V(3M + ρ) = 2^e M + v`, `invStepExp`,
  `invStepOff`), `amusicalInv_iterate_cylinder_aux`.  The bounds `0 ≤ s < 2^a` come straight
  from the induction (`r' = 2^e q + v < 2^e 3^k`, so the carry `j < 2^e`), not from the
  `n = −1` sign argument in the kickoff.
- `PrefixRoot.lean`: `sum_three_adic_ne_zero` (top term `e_n 2^{a_n}` prime to `3`, the rest a
  multiple of `3` after clearing `3^{n+1}`).  SQG1 sums over the filter of nonzero branches in
  `[i, j)` and takes its max.  The hypothesis `hj : j ≤ w.length` is not needed.
- `SquareCount.lean`: `even_run_mul`/`even_run_len` (an all-even run from `≥ 1` to `≤ H²` has
  length `≤ 6 log(2 + H)`, via `log(3/2) ≥ 1/3`); `card_small_square_times_le` (a
  repetition-free window has `≤ (|C| + 12) log(2 + H) + 3` visits to `q²`, `1 ≤ q ≤ H`: either
  some middle visit has odd steps on both sides, and SRC bounds the span, or the visits split
  into an all-even run from the first visit and one ending at the last);
  `exists_injective_window` (cycle: one period from `x`; aperiodic: from the earliest `ℤ`-time);
  `exists_nat_gt_log_bound` (`log x ≤ 2 √x`).  The main proof counts the `H` squares
  `1², …, H²` over the finitely many orbits.

Nothing open in this file.
