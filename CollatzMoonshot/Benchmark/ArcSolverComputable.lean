/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Benchmark.ArcSolverInclusion

/-!
# A computable solver step, so the fixed-`k` exclusions stop trusting Python

`ArcSolverInclusion.no_kRelaxedStrategy_of_sweep` reduces "no `k`-memory winner at `β`" to an empty
solver descent at every width of a mesh, for any code operator containing the rounded open step
`roundInRes N ∘ resStepOpen`.  Here the code operator is written in Lean over exact rational
interval lists (a transcription of `experiments/arc_sweep_rs`, which is itself written from the
spec), so that

* `stepCode_sound` proves it contains the rounded open step (the old trusted hypothesis (c)), and
* the sweep is a `native_decide` computation.

Direction for the treadmill: `ARC-SOLVER-COMPUTABLE-DIRECTION.md` at the repo root.
-/

namespace CollatzMoonshot.Benchmark.ArcSolverComputable

open ArcSolverInclusion

/-- A finite union of closed rational intervals. -/
abbrev IvList := List (ℚ × ℚ)

/-- Its real points. -/
def ivSet (L : IvList) : Set ℝ := {x | ∃ p ∈ L, ((p.1 : ℚ) : ℝ) ≤ x ∧ x ≤ ((p.2 : ℚ) : ℝ)}

/-- Drop degenerate intervals, sort by left end, merge overlaps. -/
def normIv (L : IvList) : IvList :=
  let s := (L.filter fun p => decide (p.1 < p.2)).mergeSort (fun p q => decide (p.1 ≤ q.1))
  s.foldl (fun acc p =>
    match acc with
    | [] => [p]
    | q :: rest => if p.1 ≤ q.2 then (q.1, max q.2 p.2) :: rest else p :: q :: rest) [] |>.reverse

/-- Pairwise intersections. -/
def interIv (A B : IvList) : IvList :=
  normIv (A.flatMap fun p => B.filterMap fun q =>
    let lo := max p.1 q.1
    let hi := min p.2 q.2
    if lo < hi then some (lo, hi) else none)

/-- Residue-form open step at residue `r` (memory `k ≥ 1`, arc `[s, s + t]`, width `l`): the closures
of the open start sets `(g0 - l/3, g1)` over good-move pieces, clipped to `[0, 1]`.  Floors `J = 0 … 5`
and arc lifts `m = -2 … 5` cover every legal move (`ArcSolverInclusion.enum_ranges`). -/
def stepCode (k : ℕ) (s t l : ℚ) (P : ℕ → IvList) (r : ℕ) : IvList :=
  let half := 2 ^ (k - 1)
  let d : ℚ := if r % 2 = 1 then 1 / 2 else 0
  let w := 2 * l / 3
  let arc : IvList :=
    if w < t then normIv ((List.range 8).map fun i => ((i : ℚ) - 2 + s, (i : ℚ) - 2 + s + t - w))
    else []
  let good : IvList := (List.range 6).flatMap fun J =>
    let b := ((3 * r - r % 2) / 2 + J) % half
    let tgt := interIv (P b) (P (b + half))
    interIv (normIv (tgt.map fun p => (((J : ℚ) + p.1 - d) * 2 / 3, ((J : ℚ) + p.2 - d) * 2 / 3))) arc
  normIv (good.map fun g => (max (g.1 - l / 3) 0, min g.2 1))

/-- Grid cells `[i/N, (i+1)/N]` for the half-open cells `[i/N, (i+1)/N)` inside the open interval
`(lo, hi)` (cells start strictly after `lo`, except at the clip point `0`, and may end at `hi`).  The
closed output over-includes relative to `roundInRes`, the safe direction. -/
def roundCode (N : ℕ) (L : IvList) : IvList :=
  normIv (L.filterMap fun p =>
    let i0 : ℤ := if p.1 = 0 then 0 else ⌊p.1 * (N : ℚ)⌋ + 1
    let i1 : ℤ := ⌊p.2 * (N : ℚ)⌋
    if i0 < i1 then some ((i0 : ℚ) / N, (i1 : ℚ) / N) else none)

/-- One descent step on all `2^k` residues. -/
def descendStep (k N : ℕ) (s t l : ℚ) (P : ℕ → IvList) : ℕ → IvList := fun r =>
  interIv (P r) (roundCode N (stepCode k s t l P r))

/-- Descent with fuel, from `[0, 1]` everywhere; `true` when every residue is empty. -/
def descendsEmpty (k N : ℕ) (s t l : ℚ) : ℕ → (ℕ → IvList) → Bool
  | 0, _ => false
  | fuel + 1, P =>
    if (List.range (2 ^ k)).all fun r => (P r).isEmpty then true
    else
      let P' := descendStep k N s t l P
      -- memoize the new family as a list so the next step does not recompute it
      let tab := (List.range (2 ^ k)).map P'
      descendsEmpty k N s t l fuel fun r => tab.getD r []

/-- The full sweep: every width `i δ`, `1 ≤ i`, `i δ ≤ 3t'/2`, on the arc `[β', 1 - β']`. -/
def sweepEmpty (k N : ℕ) (β' δ : ℚ) (fuel : ℕ) : Bool :=
  let t' := 1 - 2 * β'
  let imax := ⌊3 * t' / 2 / δ⌋.toNat
  (List.range imax).all fun i =>
    descendsEmpty k N β' t' ((i + 1 : ℕ) * δ) fuel fun _ => [(0, 1)]

/-! ### Targets (treadmill)  -/

/-- Intersections lose only isolated points: any interval `[x, y)` with `x < y` lying in both unions lies
in `interIv`.  (A finite union of closed intervals covering `[z, z + η)` has one interval containing `z`
and a right neighbourhood; the two such intervals meet in a nondegenerate piece.) -/
theorem Ico_subset_ivSet_interIv {A B : IvList} {x y : ℝ} (hxy : x < y)
    (hA : Set.Ico x y ⊆ ivSet A) (hB : Set.Ico x y ⊆ ivSet B) : Set.Ico x y ⊆ ivSet (interIv A B) := by
  sorry

/-- **(c), proved instead of trusted.**  The code step contains the rounded open step, on any sub-arc
of `[0, 1]` with width at most `3/2` (where `ArcSolverInclusion.enum_ranges` bounds the floors and
lifts the code enumerates). -/
theorem stepCode_sound {k N : ℕ} (hk : 1 ≤ k) (hN : 0 < N) {s t l : ℚ} (hs : 0 ≤ s) (hst : s + t ≤ 1)
    (hl0 : 0 < l) (hl : l ≤ 3 / 2) (P : ℕ → IvList) (r : ℕ) :
    roundInRes N (resStepOpen s t l k (fun r => ivSet (P r)) r) ⊆
      ivSet (roundCode N (stepCode k s t l P r)) := by
  sorry

/-- The code descent keeps every residue-form rounded post-fixed point made of half-open grid cells
(the analogue of `ArcSolverInclusion.descend_keeps` for the computed iteration); in particular
`descendsEmpty … = true` forces every such `Q` to be empty. -/
theorem descendsEmpty_excludes {k N : ℕ} (hk : 1 ≤ k) (hN : 0 < N) {s t l : ℚ} (hs : 0 ≤ s)
    (hst : s + t ≤ 1) (hl0 : 0 < l) (hl : l ≤ 3 / 2) {fuel : ℕ}
    (hE : descendsEmpty k N s t l fuel (fun _ => [(0, 1)]) = true) {Q : ℕ → Set ℝ}
    (hQ0 : ∀ r, Q r ⊆ Set.Ico 0 1)
    (hcells : ∀ r, ∀ a ∈ Q r, ∃ i : ℕ, (i : ℝ) / N ≤ a ∧ a < ((i : ℝ) + 1) / N ∧
      Set.Ico ((i : ℝ) / N) (((i : ℝ) + 1) / N) ⊆ Q r)
    (hQ : ∀ r, Q r ⊆ roundInRes N (resStepOpen s t l k Q r)) :
    ∀ r, Q r = ∅ := by
  sorry

/-- **End to end with the code in Lean**: an empty computed sweep excludes every live `k`-memory relaxed
strategy at `β` (any width).  Follows `ArcSolverInclusion.no_kRelaxedStrategy_of_sweep`'s proof with
`ArcFattening.kToLiftedBridge`, using `descendsEmpty_excludes` in place of the abstract descent. -/
theorem no_kRelaxedStrategy_of_codeSweep {k N fuel : ℕ} (hk : 1 ≤ k) (hN : 0 < N) {β e0 δ : ℚ}
    (he0 : 0 < e0) (hNe : (1 : ℚ) / N ≤ e0 / 96) (hδ : 0 < δ) (hδe : δ ≤ e0 / 2)
    (hβ0 : e0 / 2 ≤ β) (hβ1 : β ≤ 1 / 2)
    (hsweep : sweepEmpty k N (β - e0 / 2) δ fuel = true)
    {l : ℝ} {P : ℕ → Set ℝ} (hne : ∃ r < 2 ^ k, (P r).Nonempty) :
    ¬ ArcTrap.KRelaxedStrategy (β : ℝ) (1 - 2 * β) l k P := by
  sorry

/-- The computation, `k = 1`: `β = 7/57 + 1/1000`, `e0 = 1/1000`, `δ = 1/2500`, `N = 2^17`. -/
theorem sweep_7_57_plus_k1 : sweepEmpty 1 (2 ^ 17) (7 / 57 + 1 / 2000) (1 / 2500) 400 = true := by
  native_decide

/-- **No 1-memory relaxed strategy at `β = 7/57 + 1/1000`** (template for `k = 2, …, 6`: add
`sweep_7_57_plus_k*` by `native_decide` and the matching corollary). -/
theorem no_kRelaxedStrategy_7_57_plus_k1 (l : ℝ) (P : ℕ → Set ℝ) (hne : ∃ r < 2 ^ 1, (P r).Nonempty) :
    ¬ ArcTrap.KRelaxedStrategy ((7 / 57 + 1 / 1000 : ℚ) : ℝ) (1 - 2 * (7 / 57 + 1 / 1000 : ℚ)) l 1 P :=
  no_kRelaxedStrategy_of_codeSweep (N := 2 ^ 17) (fuel := 400) (e0 := 1 / 1000) (δ := 1 / 2500)
    le_rfl (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by convert sweep_7_57_plus_k1 using 3; norm_num) hne

end CollatzMoonshot.Benchmark.ArcSolverComputable
