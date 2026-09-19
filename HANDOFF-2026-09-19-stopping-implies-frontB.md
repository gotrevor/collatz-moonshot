# HANDOFF 2026-09-19 — `StoppingCorrect → NoNontrivialCycle` proved

Bounded helper lap per the 2026-09-18 attended override in `DIRECTION.md`.  Done; no
successor selected.

## Checkpoint

* Branch: `main` (no push; host pushes).
* HEAD at time of proof commit: `94076e2` "Prove StoppingCorrect implies NoNontrivialCycle at the orbit minimum".
* `lake build`: green, 8777 jobs (pre-commit hook re-verified).
* Treadmill STOP signalled via `box done --green`; no successor lap selected.

## What landed

New module `CollatzMoonshot/FrontA/FirstCrossingCycles.lean` (plus its root import in
`CollatzMoonshot.lean`).  Nothing else touched; all frozen inputs
(`FrontA.FirstCrossing.At`, `StoppingCorrect`, `CrossingExists`, every statement in
`FrontA/FirstCrossing.lean`) are unchanged.

```
theorem noNontrivialCycle_of_stoppingCorrect (h : StoppingCorrect) : NoNontrivialCycle
```
`#print axioms` → `[propext, Classical.choice, Quot.sound]`.  No `sorry`, no citation
axiom, no `native_decide`.  `lake build`: 8777 jobs, clean.

Supporting lemmas, both axiom-clean:
* `tstep_iterate_one` — the accelerated orbit of `1` is `{1,2}` (mirror of the existing
  `FrontB.tstep_iterate_two`).
* `full_period_subcritical` — for a `tstep`-cycle `tstep^[p] n = n` with `n ≥ 1`, `p > 0`:
  `3 ^ ones (traceWord n p) < 2 ^ p`.
* `tstep_cycle_member_trivial_of_stoppingCorrect` — under `StoppingCorrect` every
  accelerated cycle member is `1` or `2`.

## The mathematical content

`CrossingExists` is **not needed** for the cycle front: a cycle manufactures its own
crossing.  Over one full period the iterate identity reads
`2^p · n = 3^(ones w) · n + numer w` with `numer w > 0` (`ones_pos_of_cycle` +
`numer_pos`), so `3^(ones w) < 2^p` outright — the whole period is subcritical.

The proof then runs at the **orbit minimum**: `n₀ := Nat.find` on
`{x | ∃ i, tstep^[i] n = x}` is `tstep`-periodic with the same period `p` and is `≤`
every point of its own orbit.  If `n₀ ≥ 2`, `exists_first_crossing` applied to the
period-`p` crossing yields `At n₀ m`, and `StoppingCorrect` gives `tstep^[m] n₀ < n₀`,
contradicting minimality.  So `n₀ = 1`; walking back around the cycle
(`tstep^[p*(i₀+1) - i₀] 1 = n`) puts the accelerated member in `{1,2}`, and the existing
`tstep_cycle_of_step_cycle` / `step_member_trivial` dictionary pair lands the original
`step`-member in `{1,2,4}`.

**Implication.**  `StoppingCorrect` is not a Front A-only statement: it already contains
all of Front B.  Front B is therefore a lower bound on the difficulty of the coefficient
stopping-time conjecture, which is the honest reason
`conjecture_of_stoppingCorrect_and_crossingExists` is not a cheap route to the
conjecture — `CrossingExists` is the *only* genuinely Front A-flavoured half of that
hypothesis pair.

No missing hypothesis was exposed; the target statement was provable as written.

## Exact next steps (for whoever picks the tree up)

This helper task is closed; the override forbade selecting a successor, so the next
session should re-read `DIRECTION.md` for a fresh attended override rather than
inheriting a thread from this lap.  If none is posted, the standing frontier is the
one described in `HANDOFF-2026-09-16-eliahou-frontier-node.md` (FrontB Eliahou bound at
the 2^68 frontier) and the open-node inventory in `PENDING_WORK.md`.

Two concrete, small follow-ups this lap makes available (neither started):

1. `CrossingExists` is now the *sole* Front A-flavoured half of
   `conjecture_of_stoppingCorrect_and_crossingExists`.  Worth recording in
   `FRONT-A-ROUTES.md` that `StoppingCorrect` alone already implies Front B, so any
   route claiming `StoppingCorrect` is "the easy front" is mis-scoped.
2. `full_period_subcritical` (this module) is a reusable statement: any lemma that
   currently re-derives `3 ^ ones (traceWord n p) < 2 ^ p` from the iterate identity for
   a cycle can call it instead.

## Blockers

None.  Task complete.
