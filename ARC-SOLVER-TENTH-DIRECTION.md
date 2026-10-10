# Direction: close `no_kRelaxedStrategy_7_57_plus_tenth` (k ≤ 3 at 7/57 + 1/10000)

Target: `ArcSolverInclusion.no_kRelaxedStrategy_7_57_plus_tenth` is the last `sorry` of the fixed-k chain.  It
moves into `CollatzMoonshot/Benchmark/ArcSolverComputable.lean` (the same file and template as
`no_kRelaxedStrategy_7_57_plus`, which is proved).  Done when it is proved there, the `ArcSolverInclusion` copy is
deleted, and `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` and `native_decide` axioms.

## Parameters (already checked against `no_kRelaxedStrategy_of_codeSweep`'s hypotheses)

- `β = 7/57 + 1/10000`, `e0 = 1/10000`, so the swept arc is `β - e0/2 = 7/57 + 1/20000`.
- `N = 2^20`: `1/N ≤ e0/96` holds (`2^20 = 1048576 ≥ 960000`).
- `δ = 1/20001 ≤ e0/2 = 1/20000`.
- `fuel = 600` (the Rust descent needs at most 16 steps at `k = 1` on sampled widths).
- Rust (`experiments/arc_sweep_rs`, `arc_sweep sweep 1 3 70057/570000 1/10000 1/20001 20`): empty at all 22629
  widths for `k = 1, 2, 3`, on the rounding-fixed binary.

## Order of work

1. `sweep_7_57_tenth_k1 : sweepEmpty 1 (2^20) (7/57 + 1/20000) (1/20001) 600 = true := by native_decide`, then the
   `k = 1` corollary on the `no_kRelaxedStrategy_7_57_plus_k1` template.  Measured `#eval` cost: see below.
2. The same for `k = 2, 3`.
3. `no_kRelaxedStrategy_7_57_plus_tenth` by `interval_cases k` (the `no_kRelaxedStrategy_7_57_plus` template),
   docstring moved from `ArcSolverInclusion`; delete the old sorried copy and fix references
   (`grep -rn no_kRelaxedStrategy_7_57_plus_tenth`).

If a `native_decide` exceeds ~30 min, stop at the largest `k` that fits and record that in the handoff.  If a
sweep evaluates to `false`, that is a finding (the Lean operator and Rust disagree): stop and write it up with
the failing width, do not change parameters to make it pass.

## Rules

- Edit `ArcSolverComputable.lean`, `ArcSolverInclusion.lean` (only to delete the moved theorem), and this file.
- Never weaken a statement.  Commit green after each item.

## Measured costs

- `#eval sweepEmpty 1 (2^20) (7/57 + 1/20000) (1/20001) 600` = `true`, 44 s, 5.7 GB RSS (2026-10-10).  At `2^17`, `k = 3`
  cost about 5 times `k = 1`, so expect a few minutes for `k = 3` here.
- DONE (2026-10-10): `no_kRelaxedStrategy_7_57_plus_tenth` proved in `ArcSolverComputable` for `k = 1, 2, 3`; full module
  build 1912 s (all three sweeps together).  Axioms: `propext`, `Classical.choice`, `Quot.sound`, three `native_decide`.
