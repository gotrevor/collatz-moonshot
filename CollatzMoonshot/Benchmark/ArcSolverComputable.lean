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

/-! ### `normIv` and `interIv` -/

/-- The merge step of `normIv`. -/
def mstep (acc : IvList) (p : ℚ × ℚ) : IvList :=
  match acc with
  | [] => [p]
  | q :: rest => if p.1 ≤ q.2 then (q.1, max q.2 p.2) :: rest else p :: q :: rest

theorem normIv_eq (L : IvList) : normIv L =
    (((L.filter fun p => decide (p.1 < p.2)).mergeSort (fun p q => decide (p.1 ≤ q.1))).foldl
      mstep []).reverse := rfl

/-- `p` is covered by a piece of `acc`. -/
def Cov (acc : IvList) (q : ℚ × ℚ) : Prop := ∃ p ∈ acc, p.1 ≤ q.1 ∧ q.2 ≤ p.2

theorem cov_mstep {acc : IvList} {q : ℚ × ℚ} (h : Cov acc q) (x : ℚ × ℚ) : Cov (mstep acc x) q := by
  obtain ⟨p, hp, h1, h2⟩ := h
  match acc, hp with
  | a :: rest, hp =>
    unfold mstep
    simp only
    split_ifs with hx
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨_, List.mem_cons_self, h1, h2.trans (le_max_left _ _)⟩
      · exact ⟨p, List.mem_cons_of_mem _ hp, h1, h2⟩
    · exact ⟨p, List.mem_cons_of_mem _ hp, h1, h2⟩

theorem cov_foldl {acc : IvList} {q : ℚ × ℚ} (h : Cov acc q) (xs : IvList) :
    Cov (xs.foldl mstep acc) q := by
  induction xs generalizing acc with
  | nil => exact h
  | cons x xs ih => exact ih (cov_mstep h x)

theorem mem_mstep_fst {acc : IvList} {x p : ℚ × ℚ} (hp : p ∈ mstep acc x) :
    p.1 = x.1 ∨ ∃ p' ∈ acc, p.1 = p'.1 := by
  unfold mstep at hp
  match acc with
  | [] => simp at hp; exact Or.inl (by rw [hp])
  | a :: rest =>
    simp only at hp
    split_ifs at hp with hx
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact Or.inr ⟨a, List.mem_cons_self, rfl⟩
      · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, rfl⟩
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact Or.inl rfl
      · exact Or.inr ⟨p, hp, rfl⟩

theorem cov_mstep_self {acc : IvList} {x : ℚ × ℚ} (hle : ∀ p ∈ acc, p.1 ≤ x.1) :
    Cov (mstep acc x) x := by
  unfold mstep
  match acc with
  | [] => exact ⟨x, by simp, le_rfl, le_rfl⟩
  | a :: rest =>
    simp only
    split_ifs with hx
    · exact ⟨_, List.mem_cons_self, hle a List.mem_cons_self, le_max_right _ _⟩
    · exact ⟨x, List.mem_cons_self, le_rfl, le_rfl⟩

theorem cov_foldl_self (xs : IvList) (hs : xs.Pairwise (fun p q => p.1 ≤ q.1)) :
    ∀ acc : IvList, (∀ x ∈ xs, ∀ p ∈ acc, p.1 ≤ x.1) → ∀ x ∈ xs, Cov (xs.foldl mstep acc) x := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    intro acc hacc x hx
    have hs' := List.pairwise_cons.1 hs
    rcases List.mem_cons.1 hx with rfl | hx
    · exact cov_foldl (cov_mstep_self (hacc x List.mem_cons_self)) ys
    · refine ih hs'.2 _ (fun z hz p hp => ?_) x hx
      rcases mem_mstep_fst hp with h | ⟨p', hp', h⟩
      · rw [h]; exact hs'.1 z hz
      · rw [h]; exact hacc z (List.mem_cons_of_mem _ hz) p' hp'

/-- Invariant of the merge: nondegenerate pieces, later pieces strictly to the right. -/
def MInv (acc : IvList) : Prop :=
  (∀ p ∈ acc, p.1 < p.2) ∧ acc.Pairwise (fun p q => q.2 < p.1)

theorem minv_mstep {acc : IvList} {x : ℚ × ℚ} (h : MInv acc) (hx : x.1 < x.2)
    (hle : ∀ p ∈ acc, p.1 ≤ x.1) : MInv (mstep acc x) := by
  obtain ⟨h1, h2⟩ := h
  unfold mstep
  match acc with
  | [] => exact ⟨by simpa using hx, by simp⟩
  | a :: rest =>
    simp only
    have ha := h1 a List.mem_cons_self
    have hp := List.pairwise_cons.1 h2
    split_ifs with hxa
    · refine ⟨?_, ?_⟩
      · intro p hp'
        rcases List.mem_cons.1 hp' with rfl | hp'
        · exact lt_of_lt_of_le ha (le_max_left _ _)
        · exact h1 p (List.mem_cons_of_mem _ hp')
      · exact List.pairwise_cons.2 ⟨fun q hq => hp.1 q hq, hp.2⟩
    · push Not at hxa
      refine ⟨?_, ?_⟩
      · intro p hp'
        rcases List.mem_cons.1 hp' with rfl | hp'
        · exact hx
        · exact h1 p hp'
      · refine List.pairwise_cons.2 ⟨fun q hq => ?_, h2⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hxa
        · exact (hp.1 q hq).trans (ha.trans hxa)

theorem minv_foldl (xs : IvList) (hs : xs.Pairwise (fun p q => p.1 ≤ q.1)) (hnd : ∀ x ∈ xs, x.1 < x.2) :
    ∀ acc : IvList, MInv acc → (∀ x ∈ xs, ∀ p ∈ acc, p.1 ≤ x.1) → MInv (xs.foldl mstep acc) := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    intro acc h hacc
    have hs' := List.pairwise_cons.1 hs
    refine ih hs'.2 (fun z hz => hnd z (List.mem_cons_of_mem _ hz)) _
      (minv_mstep h (hnd y List.mem_cons_self) (hacc y List.mem_cons_self)) (fun z hz p hp => ?_)
    rcases mem_mstep_fst hp with h | ⟨p', hp', h⟩
    · rw [h]; exact hs'.1 z hz
    · rw [h]; exact hacc z (List.mem_cons_of_mem _ hz) p' hp'

theorem sorted_aux (L : IvList) :
    ((L.filter fun p => decide (p.1 < p.2)).mergeSort (fun p q => decide (p.1 ≤ q.1))).Pairwise
      (fun p q => p.1 ≤ q.1) := by
  have := List.pairwise_mergeSort (le := fun p q : ℚ × ℚ => decide (p.1 ≤ q.1))
    (fun a b c h1 h2 => by simp at *; linarith) (fun a b => by simp; exact le_total _ _)
    (L.filter fun p => decide (p.1 < p.2))
  exact this.imp (fun h => by simpa using h)

/-- Every nondegenerate input interval lies inside one output piece. -/
theorem normIv_cover {L : IvList} {q : ℚ × ℚ} (hq : q ∈ L) (hlt : q.1 < q.2) :
    ∃ p ∈ normIv L, p.1 ≤ q.1 ∧ q.2 ≤ p.2 := by
  rw [normIv_eq]
  obtain ⟨p, hp, h⟩ := cov_foldl_self _ (sorted_aux L) [] (by simp) q
    (List.mem_mergeSort.2 (List.mem_filter.2 ⟨hq, by simpa using hlt⟩))
  exact ⟨p, List.mem_reverse.2 hp, h⟩

theorem normIv_minv (L : IvList) : MInv ((((L.filter fun p => decide (p.1 < p.2)).mergeSort
      (fun p q => decide (p.1 ≤ q.1))).foldl mstep [])) :=
  minv_foldl _ (sorted_aux L) (fun x hx => by
    have := List.mem_filter.1 (List.mem_mergeSort.1 hx); simpa using this.2) [] ⟨by simp, by simp⟩ (by simp)

/-- Output pieces are nondegenerate. -/
theorem normIv_lt {L : IvList} {p : ℚ × ℚ} (hp : p ∈ normIv L) : p.1 < p.2 := by
  rw [normIv_eq, List.mem_reverse] at hp
  exact (normIv_minv L).1 p hp

/-- Distinct output pieces are separated by a gap. -/
theorem normIv_sep {L : IvList} {p q : ℚ × ℚ} (hp : p ∈ normIv L) (hq : q ∈ normIv L) (hpq : p ≠ q) :
    p.2 < q.1 ∨ q.2 < p.1 := by
  rw [normIv_eq, List.mem_reverse] at hp hq
  have hS : (((L.filter fun p => decide (p.1 < p.2)).mergeSort
      (fun p q => decide (p.1 ≤ q.1))).foldl mstep []).Pairwise
      (fun p q : ℚ × ℚ => p.2 < q.1 ∨ q.2 < p.1) :=
    (normIv_minv L).2.imp (fun h => Or.inr h)
  have : Std.Symm (fun p q : ℚ × ℚ => p.2 < q.1 ∨ q.2 < p.1) := ⟨fun a b h => h.symm⟩
  exact hS.forall hp hq hpq

theorem exists_gap (xs : List ℝ) {z y : ℝ} (h : z < y) :
    ∃ m, z < m ∧ m ≤ y ∧ ∀ e ∈ xs, z < e → m ≤ e := by
  induction xs with
  | nil => exact ⟨y, h, le_rfl, by simp⟩
  | cons e xs ih =>
    obtain ⟨m, h1, h2, h3⟩ := ih
    by_cases he : z < e
    · refine ⟨min m e, lt_min h1 he, (min_le_left _ _).trans h2, ?_⟩
      intro e' he' hz
      rcases List.mem_cons.1 he' with rfl | he'
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h3 e' he' hz)
    · refine ⟨m, h1, h2, ?_⟩
      intro e' he' hz
      rcases List.mem_cons.1 he' with rfl | he'
      · exact absurd hz he
      · exact h3 e' he' hz

theorem mem_ivSet_normIv {L : IvList} {q : ℚ × ℚ} (hq : q ∈ L) (hlt : q.1 < q.2) {x : ℝ}
    (h1 : ((q.1 : ℚ) : ℝ) ≤ x) (h2 : x ≤ ((q.2 : ℚ) : ℝ)) : x ∈ ivSet (normIv L) := by
  obtain ⟨p, hp, hp1, hp2⟩ := normIv_cover hq hlt
  exact ⟨p, hp, le_trans (by exact_mod_cast hp1) h1, le_trans h2 (by exact_mod_cast hp2)⟩

/-- A right neighbourhood: a point `z` of `[x, y) ⊆ ivSet A` lies in an interval of `A` reaching
strictly past it, indeed past a uniform `m > z` (the nearest endpoint above `z`). -/
theorem exists_right_piece {A : IvList} {x y z : ℝ} (hA : Set.Ico x y ⊆ ivSet A) (hz : z ∈ Set.Ico x y)
    (m : ℝ) (hm : z < m) (hmy : m ≤ y)
    (hgap : ∀ e ∈ A.flatMap (fun p => [((p.1 : ℚ) : ℝ), ((p.2 : ℚ) : ℝ)]), z < e → m ≤ e) :
    ∃ a ∈ A, ((a.1 : ℚ) : ℝ) ≤ z ∧ m ≤ ((a.2 : ℚ) : ℝ) := by
  obtain ⟨a, ha, h1, h2⟩ := hA (show (z + m) / 2 ∈ Set.Ico x y from
    ⟨by linarith [hz.1], by linarith⟩)
  have hmem1 : ((a.1 : ℚ) : ℝ) ∈ A.flatMap (fun p => [((p.1 : ℚ) : ℝ), ((p.2 : ℚ) : ℝ)]) :=
    List.mem_flatMap.2 ⟨a, ha, by simp⟩
  have hmem2 : ((a.2 : ℚ) : ℝ) ∈ A.flatMap (fun p => [((p.1 : ℚ) : ℝ), ((p.2 : ℚ) : ℝ)]) :=
    List.mem_flatMap.2 ⟨a, ha, by simp⟩
  refine ⟨a, ha, ?_, hgap _ hmem2 (by linarith)⟩
  by_contra hc
  have := hgap _ hmem1 (by linarith)
  linarith

/-! ### Targets (treadmill)  -/

/-- Intersections lose only isolated points: any interval `[x, y)` with `x < y` lying in both unions lies
in `interIv`.  (A finite union of closed intervals covering `[z, z + η)` has one interval containing `z`
and a right neighbourhood; the two such intervals meet in a nondegenerate piece.) -/
theorem Ico_subset_ivSet_interIv {A B : IvList} {x y : ℝ} (_hxy : x < y)
    (hA : Set.Ico x y ⊆ ivSet A) (hB : Set.Ico x y ⊆ ivSet B) : Set.Ico x y ⊆ ivSet (interIv A B) := by
  intro z hz
  obtain ⟨m, hm, hmy, hgap⟩ := exists_gap ((A ++ B).flatMap
    (fun p => [((p.1 : ℚ) : ℝ), ((p.2 : ℚ) : ℝ)])) hz.2
  obtain ⟨a, ha, ha1, ha2⟩ := exists_right_piece hA hz m hm hmy
    (fun e he hze => hgap e (by rw [List.flatMap_append]; exact List.mem_append_left _ he) hze)
  obtain ⟨b, hb, hb1, hb2⟩ := exists_right_piece hB hz m hm hmy
    (fun e he hze => hgap e (by rw [List.flatMap_append]; exact List.mem_append_right _ he) hze)
  have hlt : max a.1 b.1 < min a.2 b.2 := by
    have : ((max a.1 b.1 : ℚ) : ℝ) < ((min a.2 b.2 : ℚ) : ℝ) := by
      push_cast
      exact lt_of_le_of_lt (max_le ha1 hb1) (lt_of_lt_of_le hm (le_min ha2 hb2))
    exact_mod_cast this
  refine mem_ivSet_normIv (q := (max a.1 b.1, min a.2 b.2)) ?_ hlt ?_ ?_
  · refine List.mem_flatMap.2 ⟨a, ha, List.mem_filterMap.2 ⟨b, hb, ?_⟩⟩
    simp [hlt]
  · push_cast; exact max_le ha1 hb1
  · push_cast; exact le_min (by linarith) (by linarith)

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
