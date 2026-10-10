# Direction: kernel-check the arc solver (remove trusted hypothesis (c))

Target file: `CollatzMoonshot/Benchmark/ArcSolverComputable.lean`.  Done when it has no `sorry` and
`#print axioms no_kRelaxedStrategy_7_57_plus_k1` shows no `sorryAx` (native_decide's
`Lean.ofReduceBool` is expected and fine).

## Context (read, don't re-derive)

- `ArcSolverInclusion.lean` (proved, axiom-clean): `roundIn`, `stepOpen`, `resStepOpen`, `roundInRes`,
  the residue chain, `descend_keeps`, `enum_ranges`, `width_net`, and the end-to-end
  `no_kRelaxedStrategy_of_sweep`.  Its proof is the template for `no_kRelaxedStrategy_of_codeSweep`.
- `ArcFattening.lean` (Astra's file, proved): `kToLiftedBridge`, `robust_fatten`, `physicalize_live`,
  `residualize_live`, `residualize_subset`.  Do not edit it.
- `ArcSolverComputable.lean`: computable `IvList` operator (`normIv`, `interIv`, `stepCode`,
  `roundCode`, `descendStep`, `descendsEmpty`, `sweepEmpty`), transcribed from
  `experiments/arc_sweep_rs/src/main.rs`.  Known-answer controls pass under `#eval` (k=3 winner does not
  empty, k=2 loser empties, winner below 7/57 survives); `sweep_7_57_plus_k1` is `native_decide`d.

## Order of work

1. `Ico_subset_ivSet_interIv` (finite closed-interval unions; the docstring sketches the argument).
   You will want small lemmas: `ivSet_normIv` (normIv keeps every point of a nondegenerate interval;
   merging only enlarges), `mem_ivSet_interIv`.
2. `stepCode_sound`.  The crux.  Unfold `resStepOpen` at a point of a cell `[i/N, (i+1)/N)`: an open
   move interval `[u - μ, u + μ]`, legal, children in both lifts.  Shrink it to lie in one floor `J`
   (`ArcSolverInclusion.enum_ranges` gives `J ≤ 2 < 6` and the arc lift in `-1..1 ⊆ -2..5`); its
   `c`-image lies in `ivSet (interIv (P b) (P (b + half)))` (step 1), so `u` lies in a nondegenerate
   `good` piece `[g0, g1]`, so the start lies in the open `(g0 - l/3, g1)`, so the whole Ico cell does,
   so `roundCode` keeps the closed cell.  `roundCode` keeps cells starting strictly after `lo` (or at the
   clip point 0) and ending at or before `hi` (`⌊hi N⌋`); do NOT change that convention, it is the
   sound one (2026-10-10 fix).
   If `stepCode_sound` is false as stated, say so in a HANDOFF with the counterexample; do not weaken
   the statement silently.
3. `descendsEmpty_excludes`: induction on fuel, invariant `Q r ⊆ ivSet (P r)` for the current family,
   using `stepCode_sound`, `resStepOpen` monotonicity (`ArcSolverInclusion.resStepOpen_mono`) and step 1
   on each Ico cell (`hcells`).
4. `no_kRelaxedStrategy_of_codeSweep`: copy `no_kRelaxedStrategy_of_sweep`'s proof; the residualized
   fattened set is made of half-open cells (`roundIn` membership is half-open), and `sweepEmpty`'s
   `List.range imax` index `i` corresponds to width `(i + 1) δ`.  Casts ℚ → ℝ throughout.
5. Add `sweep_7_57_plus_k2 … k6` by `native_decide` and the corollaries
   `no_kRelaxedStrategy_7_57_plus_k2 … k6` on the `_k1` template.  Measured `#eval` costs: k=1 ~5 s,
   k=3 ~25 s; k=6 is being timed (expect minutes).  If a `native_decide` exceeds ~20 min, stop at the
   largest k that fits and record that in the handoff.

## Rules

- Only edit `ArcSolverComputable.lean` (and this file / a HANDOFF).  Other files have other owners.
- Never weaken a statement to make it provable.  A refutation is progress: record it.
- Commit green after each item.
