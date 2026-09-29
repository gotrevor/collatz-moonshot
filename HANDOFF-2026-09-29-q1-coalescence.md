# HANDOFF 2026-09-29 — Q1 coalescence and hard-shadow separation

Checkpoint: branch `main`, HEAD `a2844bb` ("Prove the eight frozen Q1
coalescence and hard-shadow separation targets").  Root `lake build` green
(8821 jobs), verified by the pre-commit hook at that commit.  Task complete;
`box done --green` was signalled.  No work is in flight.

Scope: `CollatzMoonshot/Obstructions/Q1Coalescence.lean` only (plus this doc).

All eight frozen statements are proved; no `sorry`, no new axioms.
Definitions (`branchQ`, `hardParam`) and all eight theorem types are byte-for-byte
the staged skeleton.  Every claim is about the actual `FrontB.tstep`.

## What was proved

1. `tstep_iterate_pow_two_offset` — the cylinder offset
   `T^[k](x + 2^k·d) = T^[k]x + 3^(ones (traceWord x k))·d`, by induction on `k`
   generalizing `x, d`.  One step from `x + 2^(k+1)d` shares `x`'s parity and
   equals `T x + 2^k·d` (even) or `T x + 2^k·(3d)` (odd); the recursive
   `traceWord` equation supplies the exponent bookkeeping.

2. `near_one_cycle_le_double` — split `1 + 2^K u = 1 + 2^j·(2^(K-j) u)` and apply (1).
   Base orbit facts come from `one_orbit_pair`: `T^[2i]1 = 1`, `T^[2i+1]1 = 2`,
   with odd counts `i` and `i+1`, proved by induction using
   `traceWord 1 (m+2) = true :: false :: traceWord 1 m`.  Hence
   `ones (traceWord 1 j) = (j+1)/2` and the multiplier obeys
   `3^((j+1)/2) · 2^(K-j) ≤ 2^(j+1) · 2^(K-j) = 2^(K+1)`, which is exactly the
   `3/4`-per-two-steps contraction in the form needed.

3. `branchQ_eleven` — `T^[11]105 = 38`, `ones (traceWord 105 11) = 6`,
   `T^[11]2837 = 38`, `ones (traceWord 2837 11) = 3`, all by kernel `decide`.
   Offsets `d = t` and `d = 27t` then give the common endpoint `38 + 729t`
   (`3^3·27 = 729` compensates the second offset).

4. `cubic_seventh` — `CubicCarry.cubic_carry_sixth` gives `T^[6](cubicN s) = 18q+1`,
   an odd number, so one more actual step yields `27q+2`.

5. `hardParam_eighteen_meets_q1` — `cubicQ1 (hardParam t) = branchQ (322446787 + 1372031325t)`,
   then `18 = 11 + 7` with `Function.iterate_add_apply` and both halves of (3).

6. `hardParam_descends_at_eighteen` — the common endpoint is
   `235063707761 + 1000210835925t` against `cubicN (hardParam t) = 9391943393863 + 39963308851200t`;
   constant and slope comparison, `omega`.

7. `cubicN_q1_ordered_separation` — the hard direction, exactly the kickoff route.
   `CubicPeel.cubic_peel_growth_divisibility (K+1)` supplies `s` with
   `2^(K+3) ∣ cubicP s + 1`, i.e. `T^[6](cubicN s) + 1 = 2^(K+3)·c`.
   * Non-descent: the six-term affine prefix of `cubicN` is recomputed locally
     (the `CubicCarry` copies are `private`) and each value dominates `cubicN s`.
     For depth `6+r` the local `odd_run` induction gives
     `T^[r]p + 1 = 3^r·2^(m+3)·u` whenever `p + 1 = 2^(r+m+3)·u`; the surviving
     power of two keeps every pre-step value odd, so each shortcut step rises,
     and `3^r ≥ 2^r` gives `T^[r]p ≥ p ≥ cubicN s`.
   * Auxiliary below: with `U = 2^K·c` the same divisibility gives
     `9q + 1 = 4U`, hence `q ≡ 3 (mod 4)`, so the first two auxiliary steps are
     both odd and `T^[2]q = (9q+5)/4 = 1 + U`.  Depths `j ≥ 2` are then
     `T^[j-2](1+2^K c) ≤ 2(1+U)` by (2), and `2(1+U) < cubicN s` reduces to a
     linear inequality in `s` that `omega` closes.  Depths `0,1` are direct.

8. `cubicN_q1_no_bounded_pairwise_meeting` — immediate from (7): every original
   prefix value is `≥ cubicN s` and every auxiliary prefix value is `< cubicN s`,
   so no index pair can meet.

## Scope notes

This is failure of a *uniform bounded pairwise orbit splice*, on starts with
arbitrarily long initial non-descent.  It does **not** exclude
parameter-dependent meetings and supplies no repair rank.  The affine-slope
obstruction of `RESEARCH-2026-09-29-affine-coalescence-slope.md` cannot reach
this pair (its slope ratio is `128/9`).  No convergence assumption is used
anywhere; nothing here asserts termination of any trajectory.

Helper declarations added (all `private` except the two frozen public helpers):
`two_tstep_even`, `tstep_double'`, `tstep_odd_val`, `trace_one_two`,
`one_orbit_pair`, `one_orbit`, `q1_hardParam`, `pre1`–`pre6`, `prefix_ge`,
`odd_run`, `q1_cubicN_link`, `cubicP_succ`, `aux_arith`, `aux_one`, `aux_two`.
No existing module was changed.

One tactic gotcha worth keeping: `omega` diverges (heartbeat timeout, even at
5x the limit) on goals that mix the eleven-digit progression coefficients with
a variable carrying a non-unit coefficient, e.g.
`32327709859 + 49393127700*s + 1 = 8*U ⊢ 9*(1795983881 + 2744062650*s) + 1 = 4*U`.
The fix used throughout the auxiliary side is to keep `cubicQ1 s`, `cubicN s`
and `U` as opaque atoms, tie them with the small-coefficient identity
`128*q = 9*n + 1` (proved by `ring`), and halve `cubicP s + 1 = 2*(9*q+1)` with
`Nat.eq_of_mul_eq_mul_left` rather than by omega.

Root `lake build` is green.  Nothing is in flight.

## State of the tree at handoff

Committed by this lap (the only files it owns):
- `CollatzMoonshot/Obstructions/Q1Coalescence.lean` — new, all eight frozen
  targets proved, 0 `sorry`, 0 new axioms.
- `HANDOFF-2026-09-29-q1-coalescence.md` — this doc.

Left deliberately uncommitted, because the kickoff assigns them to the parent:
- `CollatzMoonshot.lean` (modified) — adds
  `import CollatzMoonshot.Obstructions.Q1Coalescence`.  The root build above
  was run with this edit in the working tree, so it is known-green; the parent
  should commit it.
- `KICKOFF-2026-09-29-q1-coalescence.md`, `RESEARCH-2026-09-29-q1-coalescence.md`
  (untracked) — parent-owned docs.
- `experiments/repair_family.py`, `experiments/test_repair_family.py`,
  `scripts/AxiomAudit.lean` (modified) — pre-existing changes, not touched by
  this lap.

## Next steps

The bounded task is finished and the operator scope says no successor work, so
there is nothing to resume here.  For whoever picks up the thread:

1. Parent commits the root import of `CollatzMoonshot.Obstructions.Q1Coalescence`
   and adds the eight theorems to the `scripts/AxiomAudit.lean` surface if that
   file is meant to enumerate them.
2. The open mathematical questions this lap explicitly does **not** settle, in
   the kickoff's own words: parameter-dependent meetings are not excluded, and
   no repair rank is supplied.  The `-1/13` synchronous nonmeeting and the
   15-step easy-descent control remain paper observations with no Lean scope.
3. `near_one_cycle_le_double` and `tstep_iterate_pow_two_offset` are public and
   fully general (no progression constants); they are the reusable pieces if a
   later lap needs cylinder endpoints or near-`1↔2` bounds elsewhere.
