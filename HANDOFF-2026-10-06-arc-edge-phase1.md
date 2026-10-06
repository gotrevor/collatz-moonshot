# HANDOFF 2026-10-06: arc edge, phase 1 done

Kickoff: `KICKOFF-2026-10-06-arc-edge-proofs.md`.

## Result

`finiteMemory_min_arc_two_thirds` and `finiteMemoryEdgeIsTwoThirds` (`CollatzMoonshot/Benchmark/ArcTrap.lean`)
now depend only on `propext`, `Classical.choice` and `Quot.sound`.  No target statement was changed;
no hypothesis was added this lap.

Proved, in kickoff order:
1. `exists_trapped_of_relaxedStrategy`, via the general `exists_trapped_of_relaxedStrategy_from`
   (any integer part `m`, any `a ∈ P`, `ξ ∈ m + [a, a + l]`; `ξ = sup` of nested left ends).
2. `trapsResidueClass_of_relaxedStrategy` (same construction; `l ≤ 3t/2`).
3. `card_forward_le`: `fwd_fib` (two-step induction; `quarters_false` kills a full depth-2 tree).
4. `card_backward_le`: base coordinate `bbase s q = fract(2q - 3s)`, maps `phi s k`;
   `bwd_count` (full tree forces `BaseGood`), `reach_dense` (gap contraction by `2/3`).
5. `admissibleWord_growth_lt_two`, via `admissibleWord_growth_pos` (rate `ρ ∈ (7/4, 2)`):
   `exists_edge_path` (lower the start until a left edge), `admissible_ncard_le`,
   `bwd_submult`, `bwd_geom`, `fib_le_real`.
6. `finiteMemory_barrier_two_thirds`: `floorWord`, `floorWord_dvd` (2^N | g - g'),
   `trapped_ncard_le`, `trapped_ncard_ge`.

Bonus: `finiteMemory_barrier` (13/20) is now a corollary (moved after the 2/3 barrier).

## Next (phase 2, stretch)

In order: `run_bounded_count_ge` → `afsUnbroken_of_noRunLonger` → `not_afsUnbroken_of_long_run`
→ `card_afsUnbroken_le` → `near_afs_every_floor` → `near_afs_density`.

## Phase 2 progress (same day)

Proved: `run_bounded_count_ge` (ratio induction, `badExt_le`), `afsUnbroken_of_noRunLonger`
(`trail`, `afsErr_bound`), `not_afsUnbroken_of_long_run`, `card_afsUnbroken_le`
(`avoidSet_bound`, block peeling).  Branch `ren/g2-hunt-flatto-ceiling`, all committed.

Note: DIRECTION.md's 2026-09-13 directive (no execution laps) predates the 2026-10-06 operator
kickoff that assigns this work; the kickoff was treated as the newer operator instruction.

Next: `near_afs_every_floor` then `near_afs_density` (connect `afsErr` to real orbits,
anchor-parity bijection; hardest).
