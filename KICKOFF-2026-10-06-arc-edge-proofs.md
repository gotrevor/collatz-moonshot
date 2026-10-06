# KICKOFF 2026-10-06: prove the 2/3 edge theorem

**Lane:** closing hand proofs for a new result.  **Engine:** Opus/low.  **Launched 2026-10-06 on Trevor's go ("land it!").**

**Target file:** `CollatzMoonshot/Benchmark/ArcTrap.lean`.  Every target below has its English proof in its docstring.

**Headline:** `finiteMemory_min_arc_two_thirds` (and `finiteMemoryEdgeIsTwoThirds`).  It is done when `#print axioms finiteMemory_min_arc_two_thirds` shows no `sorryAx`.  The file keeps other sorries that are out of scope (the `1227`/`1228` constants, `E`, `relaxed_barrier`, `two_pow_le_card_admissibleWord`, ...).  Do not touch them, and judge progress by the headline's axioms, never by the file's sorry count.

## Phase 1: the headline, in this order

1. `exists_trapped_of_relaxedStrategy`: nested closed intervals `J_n = (m_n + [u_n, u_n + 2l/3]) / (3/2)^n`; intersection nonempty by compactness.
2. `trapsResidueClass_of_relaxedStrategy`: the same construction started at `m`.  `l ≤ 3t/2 ≤ 3/2` and `a < 1` give `⌊ξ⌋ < m + 3`.  Easiest if step 1 is first generalised to "from any `m ≥ 1` and any `a ∈ P`, with `⌊ξ⌋ ∈ [m, m + 3)`", then both follow.
3. `card_forward_le` (Fibonacci): two successors `y`, `y + 1/2`; four grandchildren spaced `1/4` need an arc of length `3/4`.
4. `card_backward_le`: the gap-shrinking argument in the docstring.
5. `admissibleWord_growth_lt_two`: decompose each word at the first time a left edge is hit, using 3 and 4.
6. `finiteMemory_barrier_two_thirds`: digits `a_n ∈ {-1/2, 0, 1/2, 1}`, injectivity (`N` digits fix `g_0 mod 2^N`), density (`≥ 2^{N-k}/3 - 1` trapped floors below `2^N + 3`), against step 5.  The hypothesis `hr : r < 2^k` was added 2026-10-06, because the class is empty otherwise (`trapsResidueClass_vacuous`).

Phase 1 is complete when the headline is axiom-clean.

## Phase 2 (stretch, only after phase 1): near-AFS bounds

In order: `run_bounded_count_ge` → `afsUnbroken_of_noRunLonger` → `not_afsUnbroken_of_long_run` → `card_afsUnbroken_le` → `near_afs_every_floor` → `near_afs_density`.  The last two connect `afsErr` to real orbits (the anchor-parity bijection); they are the hardest.

## Rules

- **Do not weaken any target statement.**  Helper lemmas are welcome, and decomposing a target into named sorried leaves is progress.
- **If a statement is false, that is the most valuable outcome.**  Write the counterexample as a Lean theorem (`¬ …`, or a concrete `decide`/`norm_num` witness), record it in `DIRECTION.md`, and stop with `box stuck`.  A hypothesis that only fixes a degenerate encoding case (like `hr` above) may be added; say so in the handoff.
- Build only `lake build CollatzMoonshot.Benchmark.ArcTrap CollatzMoonshot.Maze`.
- Do not use or build on the definition `E` (commit `3b54347`); that question is Trevor's.
- When a target lands, update its docstring's status line and the line for it in `docs/notes/arc-traps-two-thirds-edge.md` ("What is not claimed").
- Write a dated `HANDOFF-2026-10-06-arc-edge-*.md` at the end of each lap.
