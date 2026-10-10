# HANDOFF 2026-10-10 — arc solver kernel-checked

Executed `ARC-SOLVER-COMPUTABLE-DIRECTION.md`:
1. `Ico_subset_ivSet_interIv` (via `normIv_cover`, `normIv_lt`, `normIv_sep`, `exists_gap`).
2. `stepCode_sound` — TRUE as stated, proved (`good_of_start`, `piece_of_cover`, `cell_subset_roundCode`).
3. `descendsEmpty_excludes` (via `descendsEmpty_aux`, `resStepOpen_mono_lt`, `child_lt`).
4. `no_kRelaxedStrategy_of_codeSweep` (new `residualize_roundIn_cells` for the half-open cells).
5. k=1..6 sweeps + corollaries in file (native_decide standalone: k=4 149 s, k=5 246 s, k=6 584 s). DIRECTION COMPLETE.

Note: commit 4f6cf33 (another session's ArcDelayGame commit) swept in step 3's diff.

Branch `ren/g2-hunt-flatto-ceiling`, HEAD 133d41d.  `#print axioms no_kRelaxedStrategy_7_57_plus_k6` =
propext, Classical.choice, Quot.sound + its native_decide sweep.

Next steps (outside this file's scope, other owners):
- `ArcSolverInclusion.no_kRelaxedStrategy_7_57_plus` can be discharged by `interval_cases k` from the six
  `ArcSolverComputable.no_kRelaxedStrategy_7_57_plus_k*` (needs an import of ArcSolverComputable, which
  imports ArcSolverInclusion — so move the corollary or restate it downstream).
- `_tenth` (β = 7/57 + 1/10000, N = 2^20) would need a sweep 8x finer; time it before adding.
