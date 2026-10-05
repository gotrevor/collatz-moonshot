# KICKOFF 2026-10-05: prove the Flatto-ceiling statements

**Lane:** closing proofs for a Maze row.  **Engine:** Opus/low, at most three laps.  **Not launched; needs Trevor's go.**

Target: `CollatzMoonshot/Benchmark/FlattoCeiling.lean`.  Five frozen statements, each carrying its English proof in the docstring.  Do not change any statement; if one is false, stop and report.

Order: `parityWord_add_pow` → `parityWord_injective` → `zNumber_parityWord_admissible` → `card_admissible_ge` → `card_admissible_starts_ge`.  `card_admissible_ge` is the only measure-flavoured one: prove the cylinder partition and the per-cylinder length bound by induction on n, carrying the affine form of `rstep^[n]` on each cylinder.

Stop when the file is sorry-free, `lake build` is green and `#maze_audit` passes, then write a dated handoff.  No successor.

The Mahler kickoff's `IsZNumber` should import this file's definition rather than redefine it.
