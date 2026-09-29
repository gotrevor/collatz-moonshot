# HANDOFF 2026-09-29 — exact cubic carry prefixes

Bounded task from `KICKOFF-2026-09-29-cubic-carry.md`.  Complete: all five
frozen theorems in `CollatzMoonshot/Obstructions/CubicCarry.lean` compile with
no `sorry` and no new axioms.  `neighbor` and all five theorem statements are
unchanged from the staged skeleton.  `SignedFlow` and `CubicPeel` untouched.

## Checkpoint

- Branch: `main`
- HEAD at completion: `fdc04d6` ("Prove the five frozen cubic-carry prefix identities")
- Owned files this lap: `CollatzMoonshot/Obstructions/CubicCarry.lean` and this
  handoff.  Nothing else was staged; the parent's pre-existing working-tree
  edits (`CollatzMoonshot.lean`, `experiments/*.py`, `scripts/AxiomAudit.lean`,
  the `KICKOFF-*`/`RESEARCH-*` docs) were left exactly as found.
- `box done --green` called; stop sentinel at
  `~/src/.treadmill/collatz-moonshot.stop`.

## Next steps

None for this task — the acceptance condition is met in full and the kickoff
forbids successor work.  Anything further (a return-debt argument past the
six-term prefix, a repair rank, or convergence of `cubicN` itself) is parent
scope and would need its own frozen statements.

## State

`lake build` green (8820 jobs).  `#print axioms` on each target gives exactly
`[propext, Quot.sound]`:

- `cubic_carry_third`
- `cubic_carry_fifth`
- `cubic_carry_gap_unbounded`
- `cubic_carry_sixth`
- `cubic_carry_neighbor_reachesOne`

## How the proofs go

Two local step lemmas carry everything:

- `tstep_double u : tstep (2*u) = u` — the even branch of `tstep`.
- `tstep_odd_val (hu : u % 2 = 1) (h : 3*u+1 = 2*v) : tstep u = v` — the odd
  branch, pinned through `FiveHead.two_tstep_odd` plus `omega`, so each orbit
  entry is discharged by a single `ring` obligation on the affine forms.

`CubicPeel.cubicQ1_odd` is private, so `q1_odd` re-derives that parity from
`cubicQ1`'s affine form; the same pattern supplies the parity at each of the
six orbit steps (odd, odd, odd, even, odd, even — the slopes are all even, so
the parity is that of the constant).

`orbit1 … orbit6` give the affine table; `iterate_three/_five/_six` assemble it
by `show tstep (tstep …) = _`, which is definitionally the numeral iterate, so
no `Function.iterate_succ` rewriting is needed.  `neighbor_eq` derives
`neighbor s = 86207226304 + 131715007200*s` from `tstep_q1`; against
`iterate_three`'s `86207226290 + …` that is the stated offset of 14.

`neighbor_two` and `neighbor_five` peel halvings off `32 * tstep (cubicQ1 s)`
with `tstep_double`.  With `x = tstep (cubicQ1 s)`: the fifth actual iterate is
`24*x - 10` and `tstep^[2] (neighbor s) = 8*x`, which gives `cubic_carry_fifth`
directly and makes `cubic_carry_gap_unbounded` the `omega` fact
`B + 10 < 16*x` at `s = B`.

`cubic_carry_neighbor_reachesOne` uses `neighbor_five` plus
`SignedFlow.reachesOne_step_iff`: from `reachesOne (cubicQ1 s)` take
`tstep^[k] (tstep (cubicQ1 s)) = 1` and conclude at `k + 5` via
`Function.iterate_add_apply`.  No general `reachesOne_of_iterate` helper turned
out to be needed.  The target remains only the neighbor, not `cubicN`.

## Scope notes

Nothing here asserts convergence of `cubicN`, a decreasing repair rank, or any
dynamical separation beyond the six displayed finite prefixes.  No successor
work is queued; parent owns all other source and documentation.
