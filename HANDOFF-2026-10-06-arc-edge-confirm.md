# HANDOFF 2026-10-06: arc edge, confirm lap

Kickoff: `KICKOFF-2026-10-06-arc-edge-proofs.md`.  Previous baton: `HANDOFF-2026-10-06-arc-edge-phase1.md`
(it ended with `box stuck`; this is the fresh confirm lap).

## Verified from real output

- `lake build CollatzMoonshot.Benchmark.ArcTrap CollatzMoonshot.Maze`: green, 8762 jobs.
- `#print axioms` = `propext, Classical.choice, Quot.sound` for `finiteMemory_min_arc_two_thirds`,
  `finiteMemoryEdgeIsTwoThirds`, `finiteMemory_barrier_two_thirds`, `near_afs_density`,
  `near_afs_every_floor`, `card_afsUnbroken_le`, `relaxedStrategy_afs_closed`, `relaxed_barrier_13_20`.
- Statement diff: every declaration present at `485ba54` (the kickoff commit) has the same signature at HEAD;
  the relocated ones (`finiteMemory_barrier`, `near_afs_*`) were moved, not edited.
- Docstring status lines and `docs/notes/arc-traps-two-thirds-edge.md` ("What is not claimed") already say PROVED.

## Decision

The kickoff is complete, phases 1 and 2.  Every remaining `ArcTrap.lean` sorry is one the kickoff says not
to touch, and `DIRECTION.md` (CURRENT DIRECTIVE, updated this lap) has no other execution objective.  So the
right exit is `box done`, not further work.

Recorded this lap: CURRENT DIRECTIVE update + directive history (`DIRECTION.md`), STATUS top note, ledger
rows and outstanding bullet, and a ranked list of candidate next kickoffs (`PENDING_WORK.md` top).  The top
candidate is `exists_farFromIntegers_1228` (the `0.1228` record constant): soundness is now proved, so only
a finite eleven-interval certificate remains.  Cheapest: `mahler_barrier` and `relaxedStrategy_near_afs`
are now corollaries of proved theorems.

## Exit

`box done` was signalled, but the repo-wide self-stop gate declines it (20 open sorries in source, all outside
this kickoff's scope).  The kickoff was a bounded subset and this run had no `--done-when`; a future scoped
kickoff should be launched with `--done-when 'sorry-free:<target>'`.  Since every remaining sorry is either
kickoff-forbidden or under the 2026-09-13 "awaiting a new idea" directive, this lap exits with `box stuck`
(second strike after the phase-2 lap's, so the run halts for the operator).

**Operator ask:** pick the next kickoff.  Recommended: `exists_farFromIntegers_1228` together with the
corollary batch (`mahler_barrier`, `relaxedStrategy_near_afs`, `trapsResidueClass_near_afs`), launched with
`--done-when 'sorry-free:CollatzMoonshot/Benchmark/ArcTrap.lean'` scoped to those names, or explicitly name
the sorries it may touch.
