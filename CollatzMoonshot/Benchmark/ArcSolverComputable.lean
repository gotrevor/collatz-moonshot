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

/-! ### The solver step -/

/-- A cell `[i/N, (i+1)/N]` lying in a piece `p ∈ M` that starts strictly before it (or at `0`) is kept
by `roundCode`. -/
theorem cell_subset_roundCode {N : ℕ} (hN : 0 < N) {M : IvList} {p : ℚ × ℚ} (hp : p ∈ M) (i : ℕ)
    (h1 : ((p.1 : ℚ) : ℝ) < (i : ℝ) / N ∨ p.1 = 0) (h2 : ((i : ℝ) + 1) / N ≤ ((p.2 : ℚ) : ℝ)) :
    Set.Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) ⊆ ivSet (roundCode N M) := by
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  set i0 : ℤ := if p.1 = 0 then 0 else ⌊p.1 * (N : ℚ)⌋ + 1 with hi0
  set i1 : ℤ := ⌊p.2 * (N : ℚ)⌋ with hi1
  have hA : i0 ≤ i := by
    rw [hi0]; split_ifs with h0
    · positivity
    · rcases h1 with h1 | h1
      · have : p.1 < (i : ℚ) / N := by exact_mod_cast (show ((p.1 : ℚ) : ℝ) < ((i : ℚ) : ℝ) / ((N : ℚ) : ℝ) by push_cast; exact h1)
        rw [lt_div_iff₀ hN'] at this
        have : ⌊p.1 * (N : ℚ)⌋ < (i : ℤ) := Int.floor_lt.2 (by push_cast; exact this)
        omega
      · exact absurd h1 h0
  have hB : (i : ℤ) + 1 ≤ i1 := by
    have : ((i : ℚ) + 1) / N ≤ p.2 := by exact_mod_cast (show (((i : ℚ) + 1 : ℚ) : ℝ) / ((N : ℚ) : ℝ) ≤ ((p.2 : ℚ) : ℝ) by push_cast; exact h2)
    rw [div_le_iff₀ hN'] at this
    exact Int.le_floor.2 (by push_cast; exact this)
  have hlt : i0 < i1 := by omega
  have hmem : ((i0 : ℚ) / N, (i1 : ℚ) / N) ∈ M.filterMap (fun p =>
      let i0 : ℤ := if p.1 = 0 then 0 else ⌊p.1 * (N : ℚ)⌋ + 1
      let i1 : ℤ := ⌊p.2 * (N : ℚ)⌋
      if i0 < i1 then some ((i0 : ℚ) / N, (i1 : ℚ) / N) else none) :=
    List.mem_filterMap.2 ⟨p, hp, by simp only; rw [← hi0, ← hi1, if_pos hlt]⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  intro x hx
  refine mem_ivSet_normIv hmem ?_ ?_ ?_
  · show (i0 : ℚ) / N < (i1 : ℚ) / N
    exact div_lt_div_of_pos_right (by exact_mod_cast hlt) hN'
  · show (((i0 : ℚ) / N : ℚ) : ℝ) ≤ x
    push_cast
    refine le_trans (div_le_div_of_nonneg_right ?_ hNr.le) hx.1
    exact_mod_cast hA
  · show x ≤ (((i1 : ℚ) / N : ℚ) : ℝ)
    push_cast
    refine le_trans hx.2 (div_le_div_of_nonneg_right ?_ hNr.le)
    exact_mod_cast hB

/-- A half-open stretch `[x, y)` covered by intervals of `L` that each start strictly before the point
(or at `0`) lies in one piece of `normIv L`, which starts strictly before `x` (or at `0`). -/
theorem piece_of_cover {L : IvList} {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x < y)
    (hL : ∀ z ∈ Set.Ico x y, ∃ q ∈ L, ((q.1 : ℚ) : ℝ) ≤ z ∧ z < ((q.2 : ℚ) : ℝ) ∧
      (((q.1 : ℚ) : ℝ) < z ∨ q.1 = 0)) :
    ∃ p ∈ normIv L, (((p.1 : ℚ) : ℝ) < x ∨ p.1 = 0) ∧ y ≤ ((p.2 : ℚ) : ℝ) := by
  obtain ⟨q, hq, hq1, hq2, hq3⟩ := hL x ⟨le_rfl, hxy⟩
  have hqlt : q.1 < q.2 := by exact_mod_cast hq1.trans_lt hq2
  obtain ⟨p, hp, hp1, hp2⟩ := normIv_cover hq hqlt
  have hp1' : ((p.1 : ℚ) : ℝ) ≤ q.1 := by exact_mod_cast hp1
  have hp2' : ((q.2 : ℚ) : ℝ) ≤ p.2 := by exact_mod_cast hp2
  refine ⟨p, hp, ?_, ?_⟩
  · rcases hq3 with h | h
    · exact Or.inl (by linarith)
    · rcases lt_or_eq_of_le hp1 with h' | h'
      · left; rw [h] at h'; have : ((p.1 : ℚ) : ℝ) < 0 := by exact_mod_cast h'
        linarith
      · exact Or.inr (h'.trans h)
  · by_contra hc
    push Not at hc
    obtain ⟨m, hm, hmy, hgap⟩ := exists_gap ((normIv L).map fun p => ((p.1 : ℚ) : ℝ)) hc
    obtain ⟨w, hw⟩ : ∃ w : ℝ, w = ((p.2 : ℚ) : ℝ) / 2 + m / 2 := ⟨_, rfl⟩
    obtain ⟨q', hq', h1, h2, -⟩ := hL w ⟨by linarith, by linarith⟩
    have hq'lt : q'.1 < q'.2 := by exact_mod_cast h1.trans_lt h2
    obtain ⟨p', hp', hp1', hp2'⟩ := normIv_cover hq' hq'lt
    have e1 : ((p'.1 : ℚ) : ℝ) ≤ w := le_trans (by exact_mod_cast hp1') h1
    have e2 : w ≤ ((p'.2 : ℚ) : ℝ) := le_trans h2.le (by exact_mod_cast hp2')
    have hne : p ≠ p' := by
      rintro rfl; linarith
    rcases normIv_sep hp hp' hne with h | h
    · have hh : ((p.2 : ℚ) : ℝ) < p'.1 := by exact_mod_cast h
      have := hgap _ (List.mem_map.2 ⟨p', hp', rfl⟩) hh
      linarith
    · have hh : ((p'.2 : ℚ) : ℝ) < p.1 := by exact_mod_cast h
      have := normIv_lt hp
      have : ((p.1 : ℚ) : ℝ) < p.2 := by exact_mod_cast this
      linarith
/-- The arc pieces of `stepCode` (move intervals whose window fits a lift of the arc). -/
def arcIv (s t l : ℚ) : IvList :=
  let w := 2 * l / 3
  if w < t then normIv ((List.range 8).map fun i => ((i : ℚ) - 2 + s, (i : ℚ) - 2 + s + t - w))
  else []

/-- The good-move pieces of `stepCode`. -/
def goodIv (k : ℕ) (s t l : ℚ) (P : ℕ → IvList) (r : ℕ) : IvList :=
  let half := 2 ^ (k - 1)
  let d : ℚ := if r % 2 = 1 then 1 / 2 else 0
  (List.range 6).flatMap fun J =>
    let b := ((3 * r - r % 2) / 2 + J) % half
    let tgt := interIv (P b) (P (b + half))
    interIv (normIv (tgt.map fun p => (((J : ℚ) + p.1 - d) * 2 / 3, ((J : ℚ) + p.2 - d) * 2 / 3)))
      (arcIv s t l)

theorem stepCode_eq (k : ℕ) (s t l : ℚ) (P : ℕ → IvList) (r : ℕ) :
    stepCode k s t l P r =
      normIv ((goodIv k s t l P r).map fun g => (max (g.1 - l / 3) 0, min g.2 1)) := rfl

theorem dq_cast (r : ℕ) :
    (((if r % 2 = 1 then 1 / 2 else 0 : ℚ) : ℚ) : ℝ) = ((r % 2 : ℕ) : ℝ) / 2 := by
  rcases Nat.mod_two_eq_zero_or_one r with h | h <;> simp [h]

/-- **The move side of `stepCode_sound`.**  A start `z ∈ [0, 1]` with an open interval of good legal
moves around `u` sees `u` inside a good piece, so `z` lies in that piece's open start set. -/
theorem good_of_start {k : ℕ} {s t l : ℚ} (hs : 0 ≤ s) (hst : s + t ≤ 1)
    (hl0 : 0 < l) (hl : l ≤ 3 / 2) (P : ℕ → IvList) (r : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hz : z ∈ resStepOpen s t l k (fun r => ivSet (P r)) r) :
    ∃ g ∈ goodIv k s t l P r, ((g.1 : ℚ) : ℝ) - (l : ℝ) / 3 < z ∧ z < ((g.2 : ℚ) : ℝ) := by
  obtain ⟨u, μ, hμ, hu⟩ := hz
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs
  have hst' : (s : ℝ) + t ≤ 1 := by exact_mod_cast hst
  have hl0' : (0 : ℝ) < l := by exact_mod_cast hl0
  have hl' : (l : ℝ) ≤ 3 / 2 := by
    have := (Rat.cast_le (K := ℝ)).2 hl; push_cast at this; exact this
  set d : ℝ := ((r % 2 : ℕ) : ℝ) / 2 with hd
  have hd0 : 0 ≤ d := by positivity
  have hd1 : d ≤ 1 / 2 := by
    have : ((r % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 (Nat.mod_lt r two_pos)
    rw [hd]; linarith
  obtain ⟨hzu, hul, ⟨j0, hj01, hj02⟩, -⟩ := hu 0 (by simp [hμ.le])
  simp only [add_zero] at hzu hul hj01 hj02
  have hp := (hu μ (by rw [abs_of_pos hμ])).2.1
  have hm := (hu (-μ) (by rw [abs_neg, abs_of_pos hμ])).1
  have hμl : μ ≤ l / 6 := by linarith
  obtain ⟨-, -, hJ0, hJ2⟩ := enum_ranges hs' hst' hl0'.le hl' hz0 hz1 hzu (by linarith) hd0 hd1
    hj01 hj02
  set J0 := ⌊3 * u / 2 + d⌋ with hJ0def
  have hfl := Int.lt_floor_add_one (3 * u / 2 + d)
  rw [← hJ0def] at hfl
  set ε := min μ (((J0 : ℝ) + 1 - (3 * u / 2 + d)) * 2 / 3) with hε
  have hεpos : 0 < ε := lt_min hμ (by linarith)
  have hεμ : ε ≤ μ := min_le_left _ _
  have hεJ : ε ≤ ((J0 : ℝ) + 1 - (3 * u / 2 + d)) * 2 / 3 := min_le_right _ _
  have hvq : ∀ v ∈ Set.Ico u (u + ε), |v - u| ≤ μ := fun v hv => by
    rw [abs_le]; constructor <;> linarith [hv.1, hv.2]
  have hvfl : ∀ v ∈ Set.Ico u (u + ε), ⌊3 * v / 2 + d⌋ = J0 := fun v hv => by
    rw [Int.floor_eq_iff]; constructor <;> linarith [hv.1, hv.2, Int.floor_le (3 * u / 2 + d)]
  set Jn := J0.toNat with hJn
  have hJn' : (Jn : ℤ) = J0 := Int.toNat_of_nonneg hJ0
  have hJnR : ((Jn : ℚ) : ℝ) = (J0 : ℝ) := by
    rw [Rat.cast_natCast]; exact_mod_cast hJn'
  have hJnR' : ((Jn : ℕ) : ℝ) = (J0 : ℝ) := by exact_mod_cast hJn'
  have hJ6 : Jn < 6 := by omega
  -- the arc side
  have hw : 2 * l / 3 < t := by
    by_contra hc
    push Not at hc
    have hc' : (t : ℝ) ≤ 2 * l / 3 := by exact_mod_cast hc
    obtain ⟨-, -, ⟨j1, hj11, hj12⟩, -⟩ := hu (ε / 2) (by
      rw [abs_of_pos (by linarith)]; linarith)
    have e0 : u = j0 + s := by linarith
    have e1 : u + ε / 2 = j1 + s := by linarith
    have : ((j1 - j0 : ℤ) : ℝ) = ε / 2 := by push_cast; linarith
    have h1 : (0 : ℝ) < ((j1 - j0 : ℤ) : ℝ) := by rw [this]; linarith
    have h1' : 0 < j1 - j0 := by exact_mod_cast h1
    have h2 : (1 : ℝ) ≤ ((j1 - j0 : ℤ) : ℝ) := by exact_mod_cast h1'
    linarith
  have hArc : Set.Ico u (u + ε) ⊆ ivSet (arcIv s t l) := by
    intro v hv
    obtain ⟨h1, h2, ⟨j, hj1, hj2⟩, -⟩ := hu (v - u) (hvq v hv)
    simp only [add_sub_cancel] at h1 h2 hj1 hj2
    obtain ⟨hjm, hjp, -, -⟩ := enum_ranges hs' hst' hl0'.le hl' hz0 hz1 h1 (by linarith) hd0 hd1
      hj1 hj2
    unfold arcIv
    simp only
    rw [if_pos hw]
    have hidx : (((j + 2).toNat : ℕ) : ℝ) - 2 = j := by
      have : (((j + 2).toNat : ℤ)) = j + 2 := Int.toNat_of_nonneg (by omega)
      have : (((j + 2).toNat : ℕ) : ℝ) = (j : ℝ) + 2 := by exact_mod_cast this
      linarith
    have hmemq : (((j + 2).toNat : ℚ) - 2 + s, ((j + 2).toNat : ℚ) - 2 + s + t - 2 * l / 3) ∈
        (List.range 8).map (fun i : ℕ => ((i : ℚ) - 2 + s, (i : ℚ) - 2 + s + t - 2 * l / 3)) :=
      List.mem_map.2 ⟨(j + 2).toNat, List.mem_range.2 (by omega), rfl⟩
    refine mem_ivSet_normIv hmemq ?_ ?_ ?_
    · show ((j + 2).toNat : ℚ) - 2 + s < ((j + 2).toNat : ℚ) - 2 + s + t - 2 * l / 3
      linarith
    · show ((((j + 2).toNat : ℚ) - 2 + s : ℚ) : ℝ) ≤ v
      push_cast; rw [hidx]; exact hj1
    · show v ≤ ((((j + 2).toNat : ℚ) - 2 + s + t - 2 * l / 3 : ℚ) : ℝ)
      push_cast; rw [hidx]; linarith
  -- the target side
  set b := ((3 * r - r % 2) / 2 + Jn) % 2 ^ (k - 1) with hb
  set y0 := 3 * u / 2 + d - J0 with hy0
  have hT : Set.Ico y0 (y0 + 3 * ε / 2) ⊆ ivSet (interIv (P b) (P (b + 2 ^ (k - 1)))) := by
    have hboth : ∀ b' < 2, Set.Ico y0 (y0 + 3 * ε / 2) ⊆ ivSet (P (b + b' * 2 ^ (k - 1))) := by
      intro b' hb' y hy
      have hv : u + (y - y0) * 2 / 3 ∈ Set.Ico u (u + ε) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have := (hu ((y - y0) * 2 / 3) (by have := hvq _ hv; simpa using this)).2.2.2 b' hb'
      have hfl' := hvfl _ hv
      rw [hfl', Int.fract, hfl'] at this
      rw [hb]
      rw [← hJn] at this
      convert this using 2
      rw [hy0]; ring
    exact Ico_subset_ivSet_interIv (by linarith) (by simpa using hboth 0 two_pos)
      (by simpa using hboth 1 one_lt_two)
  have hX : Set.Ico u (u + ε) ⊆ ivSet (normIv ((interIv (P b) (P (b + 2 ^ (k - 1)))).map fun p =>
      (((Jn : ℚ) + p.1 - (if r % 2 = 1 then 1 / 2 else 0 : ℚ)) * 2 / 3,
        ((Jn : ℚ) + p.2 - (if r % 2 = 1 then 1 / 2 else 0 : ℚ)) * 2 / 3))) := by
    intro v hv
    obtain ⟨p, hp, hp1, hp2⟩ := hT (show 3 * v / 2 + d - J0 ∈ Set.Ico y0 (y0 + 3 * ε / 2) from
      ⟨by linarith [hv.1], by linarith [hv.2]⟩)
    have hplt := normIv_lt (show p ∈ normIv _ from hp)
    refine mem_ivSet_normIv (List.mem_map.2 ⟨p, hp, rfl⟩) (by simp only; linarith) ?_ ?_
    · push_cast; rw [hJnR', dq_cast]; linarith
    · push_cast; rw [hJnR', dq_cast]; linarith
  obtain ⟨g, hg, hg1, hg2⟩ := Ico_subset_ivSet_interIv (by linarith) hX hArc
    (show u ∈ Set.Ico u (u + ε) from ⟨le_rfl, by linarith⟩)
  refine ⟨g, List.mem_flatMap.2 ⟨Jn, List.mem_range.2 hJ6, hg⟩, by linarith, by linarith⟩

/-- **(c), proved instead of trusted.**  The code step contains the rounded open step, on any sub-arc
of `[0, 1]` with width at most `3/2` (where `ArcSolverInclusion.enum_ranges` bounds the floors and
lifts the code enumerates). -/
theorem stepCode_sound {k N : ℕ} (_hk : 1 ≤ k) (hN : 0 < N) {s t l : ℚ} (hs : 0 ≤ s) (hst : s + t ≤ 1)
    (hl0 : 0 < l) (hl : l ≤ 3 / 2) (P : ℕ → IvList) (r : ℕ) :
    roundInRes N (resStepOpen s t l k (fun r => ivSet (P r)) r) ⊆
      ivSet (roundCode N (stepCode k s t l P r)) := by
  rintro a ⟨i, hi, h1, h2, hcell⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) ≤ (i : ℝ) / N := by positivity
  have hxy : (i : ℝ) / N < ((i : ℝ) + 1) / N := div_lt_div_of_pos_right (by linarith) hN'
  have hy1 : ((i : ℝ) + 1) / N ≤ 1 := by
    rw [div_le_one hN']; exact_mod_cast hi
  obtain ⟨p, hp, hp1, hp2⟩ := piece_of_cover
    (L := (goodIv k s t l P r).map fun g => (max (g.1 - l / 3) 0, min g.2 1)) hx0 hxy (by
      intro z hz
      have hz0 : 0 ≤ z := hx0.trans hz.1
      have hz1 : z < 1 := lt_of_lt_of_le hz.2 hy1
      obtain ⟨g, hg, hg1, hg2⟩ := good_of_start hs hst hl0 hl P r hz0 hz1.le (hcell hz)
      refine ⟨_, List.mem_map.2 ⟨g, hg, rfl⟩, ?_, ?_, ?_⟩
      · push_cast; exact max_le (by linarith) hz0
      · push_cast; exact lt_min hg2 hz1
      · rcases le_total (g.1 - l / 3) 0 with h | h
        · right; exact max_eq_right h
        · left; push_cast
          have h' : (0 : ℝ) ≤ ((g.1 : ℚ) : ℝ) - (l : ℝ) / 3 := by exact_mod_cast h
          rw [max_eq_left h']; exact hg1)
  rw [stepCode_eq]
  exact cell_subset_roundCode hN hp i hp1 hp2 ⟨h1, h2.le⟩


theorem child_lt {k : ℕ} (hk : 1 ≤ k) (x b : ℕ) (hb : b < 2) :
    x % 2 ^ (k - 1) + b * 2 ^ (k - 1) < 2 ^ k := by
  have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have := Nat.mod_lt x (show 0 < 2 ^ (k - 1) by positivity)
  interval_cases b <;> omega

/-- `resStepOpen` only reads residues below `2^k`. -/
theorem resStepOpen_mono_lt {s t l : ℝ} {k : ℕ} (hk : 1 ≤ k) {P P' : ℕ → Set ℝ}
    (h : ∀ r < 2 ^ k, P r ⊆ P' r) (r : ℕ) :
    resStepOpen s t l k P r ⊆ resStepOpen s t l k P' r := by
  rintro a ⟨u, μ, hμ, hu⟩
  exact ⟨u, μ, hμ, fun q hq => ⟨(hu q hq).1, (hu q hq).2.1, (hu q hq).2.2.1,
    fun b hb => h _ (child_lt hk _ _ hb) ((hu q hq).2.2.2 b hb)⟩⟩

theorem descendsEmpty_aux {k N : ℕ} (hk : 1 ≤ k) (hN : 0 < N) {s t l : ℚ} (hs : 0 ≤ s)
    (hst : s + t ≤ 1) (hl0 : 0 < l) (hl : l ≤ 3 / 2) {Q : ℕ → Set ℝ}
    (hcells : ∀ r, ∀ a ∈ Q r, ∃ i : ℕ, (i : ℝ) / N ≤ a ∧ a < ((i : ℝ) + 1) / N ∧
      Set.Ico ((i : ℝ) / N) (((i : ℝ) + 1) / N) ⊆ Q r)
    (hQ : ∀ r, Q r ⊆ roundInRes N (resStepOpen s t l k Q r)) :
    ∀ fuel (P : ℕ → IvList), (∀ r < 2 ^ k, Q r ⊆ ivSet (P r)) →
      descendsEmpty k N s t l fuel P = true → ∀ r < 2 ^ k, Q r = ∅ := by
  intro fuel
  induction fuel with
  | zero => intro P _ h; simp [descendsEmpty] at h
  | succ n ih =>
    intro P hP hE
    rw [descendsEmpty] at hE
    split_ifs at hE with hall
    · intro r hr
      have := List.all_eq_true.1 hall r (List.mem_range.2 hr)
      have hPr : P r = [] := by simpa using this
      apply Set.eq_empty_of_subset_empty
      intro a ha
      obtain ⟨p, hp, -⟩ := hP r hr ha
      rw [hPr] at hp; simp at hp
    · refine ih _ ?_ hE
      intro r hr a ha
      have hget : ((List.range (2 ^ k)).map (descendStep k N s t l P)).getD r [] =
          descendStep k N s t l P r := by
        simp [List.getD_eq_getElem?_getD, hr]
      simp only [hget, descendStep]
      obtain ⟨i, h1, h2, hC⟩ := hcells r a ha
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      refine Ico_subset_ivSet_interIv (div_lt_div_of_pos_right (by linarith) hN')
        (hC.trans (hP r hr)) ?_ ⟨h1, h2⟩
      intro b hb
      exact stepCode_sound hk hN hs hst hl0 hl P r
        (roundInRes_mono (resStepOpen_mono_lt hk (fun r' hr' => hP r' hr') r) (hQ r (hC hb)))

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
  have hlow := descendsEmpty_aux hk hN hs hst hl0 hl hcells hQ fuel _ (fun r _ a ha =>
    ⟨(0, 1), List.mem_singleton_self _, by simpa using (hQ0 r ha).1,
      by simpa using (hQ0 r ha).2.le⟩) hE
  intro r
  by_cases hr : r < 2 ^ k
  · exact hlow r hr
  · apply Set.eq_empty_of_subset_empty
    intro a ha
    obtain ⟨i, -, h1, h2, hC⟩ := hQ r ha
    obtain ⟨u, μ, hμ, hu⟩ := hC ⟨h1, h2⟩
    have := (hu 0 (by simp [hμ.le])).2.2.2 0 two_pos
    rw [hlow _ (child_lt hk _ _ two_pos)] at this
    exact this


/-- The residue projection of a rounded set is a union of half-open residue cells. -/
theorem residualize_roundIn_cells (k N : ℕ) (hN : 0 < N) (S : Set ℝ) (r : ℕ) :
    ∀ a ∈ ArcFattening.residualize k (roundIn N S) r, ∃ i : ℕ, (i : ℝ) / N ≤ a ∧
      a < ((i : ℝ) + 1) / N ∧
      Set.Ico ((i : ℝ) / N) (((i : ℝ) + 1) / N) ⊆ ArcFattening.residualize k (roundIn N S) r := by
  rintro a ⟨x, ⟨i, hi1, hi2, hiS⟩, hres, rfl⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set m := ⌊x⌋ with hm
  have hm1 : (m : ℝ) ≤ x := Int.floor_le x
  have hm2 : x < m + 1 := Int.lt_floor_add_one x
  have hA : (i : ℝ) < (m + 1) * N := by
    have := (div_le_iff₀ hN').1 hi1; nlinarith
  have hB : (m : ℝ) * N < i + 1 := by
    have := (lt_div_iff₀ hN').1 hi2; nlinarith
  have hA' : i < (m + 1) * N := by exact_mod_cast hA
  have hB' : m * N < i + 1 := by exact_mod_cast hB
  have hA2 : i < m * N + N := by rw [add_mul, one_mul] at hA'; exact hA'
  have hc : (((i - m * N).toNat : ℕ) : ℝ) = (i : ℝ) - m * N := by
    have : ((i - m * N).toNat : ℤ) = i - m * N := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  refine ⟨(i - m * N).toNat, ?_, ?_, ?_⟩
  · rw [hc, Int.fract, div_le_iff₀ hN']
    have := (div_le_iff₀ hN').1 hi1; nlinarith
  · rw [hc, Int.fract, lt_div_iff₀ hN']
    have := (lt_div_iff₀ hN').1 hi2; nlinarith
  · intro a' ⟨ha1, ha2⟩
    rw [hc] at ha1 ha2
    have hlt1 : a' < 1 := by
      have h' : (i : ℝ) - m * N + 1 ≤ N := by
        have : i - m * N + 1 ≤ (N : ℤ) := by omega
        exact_mod_cast this
      have : ((i : ℝ) - m * N + 1) / N ≤ 1 := by rw [div_le_one hN']; exact h'
      linarith
    have hge0 : 0 ≤ a' := by
      have : (0 : ℝ) ≤ (i - m * N) / N := by
        apply div_nonneg _ hN'.le
        have : (0 : ℤ) ≤ i - m * N := by omega
        exact_mod_cast this
      linarith
    have hfl : ⌊(m : ℝ) + a'⌋ = m := by
      rw [Int.floor_eq_iff]; constructor <;> linarith
    refine ⟨m + a', ⟨i, ?_, ?_, hiS⟩, ?_, ?_⟩
    · have := (div_le_iff₀ hN').1 ha1; rw [div_le_iff₀ hN']; nlinarith
    · have := (lt_div_iff₀ hN').1 ha2; rw [lt_div_iff₀ hN']; nlinarith
    · simp only [ArcFattening.residue] at hres ⊢
      rw [hfl]; exact hres
    · rw [Int.fract, hfl]; ring

/-- **End to end with the code in Lean**: an empty computed sweep excludes every live `k`-memory relaxed
strategy at `β` (any width).  Follows `ArcSolverInclusion.no_kRelaxedStrategy_of_sweep`'s proof with
`ArcFattening.kToLiftedBridge`, using `descendsEmpty_excludes` in place of the abstract descent. -/
theorem no_kRelaxedStrategy_of_codeSweep {k N fuel : ℕ} (hk : 1 ≤ k) (hN : 0 < N) {β e0 δ : ℚ}
    (he0 : 0 < e0) (hNe : (1 : ℚ) / N ≤ e0 / 96) (hδ : 0 < δ) (hδe : δ ≤ e0 / 2)
    (hβ0 : e0 / 2 ≤ β) (_hβ1 : β ≤ 1 / 2)
    (hsweep : sweepEmpty k N (β - e0 / 2) δ fuel = true)
    {l : ℝ} {P : ℕ → Set ℝ} (hne : ∃ r < 2 ^ k, (P r).Nonempty) :
    ¬ ArcTrap.KRelaxedStrategy (β : ℝ) (1 - 2 * β) l k P := by
  intro hS
  have hl : 0 < l := hS.1
  have he0' : (0 : ℝ) < e0 := by exact_mod_cast he0
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hδe' : (δ : ℝ) ≤ e0 / 2 := by exact_mod_cast hδe
  have hNe'' : 1 / (N : ℝ) ≤ e0 / 96 := by
    have := (Rat.cast_le (K := ℝ)).2 hNe; push_cast at this; exact this
  have hL := ArcFattening.kToLiftedBridge (β : ℝ) (1 - 2 * β) l k P hk hS
  have hPne := ArcFattening.physicalize_live hS.2.1 hne
  obtain ⟨i, hi1, hi2⟩ := width_net hl.le he0' hδ' hδe'
  set e := (i : ℝ) * δ - l with he
  have he_pos : 0 < e := by linarith
  have hNe' : 1 / (N : ℝ) ≤ e / 48 := by linarith
  obtain ⟨hpost, hTne⟩ := rounded_fattened_post_fixed hL he_pos hN hNe'
  set S := thick (e / 12) ((fun x => x - e / 2) '' ArcFattening.physicalize k P)
  set T := roundIn N S
  have hwid : l + e = (i : ℝ) * δ := by rw [he]; ring
  obtain ⟨β', hβ'⟩ : ∃ x : ℚ, x = β - e0 / 2 := ⟨_, rfl⟩
  rw [← hβ'] at hsweep
  have hβR : (β' : ℝ) = β - e0 / 2 := by rw [hβ']; push_cast; ring
  have hpost' : T ⊆ roundIn N (stepOpen ((β' : ℚ) : ℝ) (((1 - 2 * β' : ℚ)) : ℝ) (((i * δ : ℚ)) : ℝ)
      (2 ^ (k - 1)) T) := by
    refine hpost.trans (roundIn_mono ?_)
    have : (((i * δ : ℚ)) : ℝ) = l + e := by rw [hwid]; push_cast; ring
    rw [this]
    exact stepOpen_arc_mono (s' := ((β' : ℚ) : ℝ)) (t' := (((1 - 2 * β' : ℚ)) : ℝ))
      (by rw [hβR]; linarith) (by push_cast; rw [hβR]; linarith) T
  have hQ := residualize_post_fixed hk hN hpost'
  have hi1' : 1 ≤ i := by
    by_contra h0
    have : i = 0 := by omega
    subst this; simp at hi1; linarith
  have hi2' : (i : ℝ) * δ ≤ 3 * (1 - 2 * β + e0) / 2 := by
    obtain ⟨r0, hr0, hP0⟩ := hne
    have := hS.width_le hr0 hP0
    linarith
  -- the sweep at width i δ
  have hiq : (i : ℚ) * δ ≤ 3 * (1 - 2 * β') / 2 := by
    have : (((i : ℚ) * δ : ℚ) : ℝ) ≤ ((3 * (1 - 2 * β') / 2 : ℚ) : ℝ) := by
      push_cast; rw [hβR]; linarith
    exact_mod_cast this
  have hE : descendsEmpty k N β' (1 - 2 * β') (((i - 1 + 1 : ℕ) : ℚ) * δ) fuel (fun _ => [(0, 1)]) = true := by
    unfold sweepEmpty at hsweep
    refine List.all_eq_true.1 hsweep (i - 1) (List.mem_range.2 ?_)
    have h1 : (i : ℚ) ≤ 3 * (1 - 2 * β') / 2 / δ := by rw [le_div_iff₀ hδ]; exact hiq
    have h2 : (i : ℤ) ≤ ⌊3 * (1 - 2 * β') / 2 / δ⌋ := Int.le_floor.2 (by exact_mod_cast h1)
    omega
  rw [show i - 1 + 1 = i by omega] at hE
  have hβ'0 : 0 ≤ β' := by rw [hβ']; linarith
  have hlq : (0 : ℚ) < i * δ := by positivity
  have hl32 : (i : ℚ) * δ ≤ 3 / 2 := by
    have : (1 - 2 * β') ≤ 1 := by rw [hβ']; linarith
    linarith
  have hempty := descendsEmpty_excludes hk hN hβ'0 (by rw [hβ']; linarith) hlq hl32 hE
    (Q := ArcFattening.residualize k T)
    (fun r => (ArcFattening.residualize_subset k T r))
    (fun r => residualize_roundIn_cells k N hN S r) hQ
  obtain ⟨r, -, a, ha⟩ := ArcFattening.residualize_live (k := k) (hTne hPne)
  rw [hempty r] at ha
  exact ha

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

/-- The computation, `k = 2` (same parameters as `sweep_7_57_plus_k1`). -/
theorem sweep_7_57_plus_k2 : sweepEmpty 2 (2 ^ 17) (7 / 57 + 1 / 2000) (1 / 2500) 400 = true := by
  native_decide

/-- **No 2-memory relaxed strategy at `β = 7/57 + 1/1000`**, any width. -/
theorem no_kRelaxedStrategy_7_57_plus_k2 (l : ℝ) (P : ℕ → Set ℝ) (hne : ∃ r < 2 ^ 2, (P r).Nonempty) :
    ¬ ArcTrap.KRelaxedStrategy ((7 / 57 + 1 / 1000 : ℚ) : ℝ) (1 - 2 * (7 / 57 + 1 / 1000 : ℚ)) l 2 P :=
  no_kRelaxedStrategy_of_codeSweep (N := 2 ^ 17) (fuel := 400) (e0 := 1 / 1000) (δ := 1 / 2500)
    (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by convert sweep_7_57_plus_k2 using 3; norm_num) hne

/-- The computation, `k = 3` (same parameters as `sweep_7_57_plus_k1`). -/
theorem sweep_7_57_plus_k3 : sweepEmpty 3 (2 ^ 17) (7 / 57 + 1 / 2000) (1 / 2500) 400 = true := by
  native_decide

/-- **No 3-memory relaxed strategy at `β = 7/57 + 1/1000`**, any width. -/
theorem no_kRelaxedStrategy_7_57_plus_k3 (l : ℝ) (P : ℕ → Set ℝ) (hne : ∃ r < 2 ^ 3, (P r).Nonempty) :
    ¬ ArcTrap.KRelaxedStrategy ((7 / 57 + 1 / 1000 : ℚ) : ℝ) (1 - 2 * (7 / 57 + 1 / 1000 : ℚ)) l 3 P :=
  no_kRelaxedStrategy_of_codeSweep (N := 2 ^ 17) (fuel := 400) (e0 := 1 / 1000) (δ := 1 / 2500)
    (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by convert sweep_7_57_plus_k3 using 3; norm_num) hne

/-- The computation, `k = 4` (same parameters as `sweep_7_57_plus_k1`). -/
theorem sweep_7_57_plus_k4 : sweepEmpty 4 (2 ^ 17) (7 / 57 + 1 / 2000) (1 / 2500) 400 = true := by
  native_decide

/-- **No 4-memory relaxed strategy at `β = 7/57 + 1/1000`**, any width. -/
theorem no_kRelaxedStrategy_7_57_plus_k4 (l : ℝ) (P : ℕ → Set ℝ) (hne : ∃ r < 2 ^ 4, (P r).Nonempty) :
    ¬ ArcTrap.KRelaxedStrategy ((7 / 57 + 1 / 1000 : ℚ) : ℝ) (1 - 2 * (7 / 57 + 1 / 1000 : ℚ)) l 4 P :=
  no_kRelaxedStrategy_of_codeSweep (N := 2 ^ 17) (fuel := 400) (e0 := 1 / 1000) (δ := 1 / 2500)
    (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by convert sweep_7_57_plus_k4 using 3; norm_num) hne

/-- The computation, `k = 5` (same parameters as `sweep_7_57_plus_k1`). -/
theorem sweep_7_57_plus_k5 : sweepEmpty 5 (2 ^ 17) (7 / 57 + 1 / 2000) (1 / 2500) 400 = true := by
  native_decide

/-- **No 5-memory relaxed strategy at `β = 7/57 + 1/1000`**, any width. -/
theorem no_kRelaxedStrategy_7_57_plus_k5 (l : ℝ) (P : ℕ → Set ℝ) (hne : ∃ r < 2 ^ 5, (P r).Nonempty) :
    ¬ ArcTrap.KRelaxedStrategy ((7 / 57 + 1 / 1000 : ℚ) : ℝ) (1 - 2 * (7 / 57 + 1 / 1000 : ℚ)) l 5 P :=
  no_kRelaxedStrategy_of_codeSweep (N := 2 ^ 17) (fuel := 400) (e0 := 1 / 1000) (δ := 1 / 2500)
    (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by convert sweep_7_57_plus_k5 using 3; norm_num) hne

/-- The computation, `k = 6` (same parameters as `sweep_7_57_plus_k1`; ~10 min standalone). -/
theorem sweep_7_57_plus_k6 : sweepEmpty 6 (2 ^ 17) (7 / 57 + 1 / 2000) (1 / 2500) 400 = true := by
  native_decide

/-- **No 6-memory relaxed strategy at `β = 7/57 + 1/1000`**, any width. -/
theorem no_kRelaxedStrategy_7_57_plus_k6 (l : ℝ) (P : ℕ → Set ℝ) (hne : ∃ r < 2 ^ 6, (P r).Nonempty) :
    ¬ ArcTrap.KRelaxedStrategy ((7 / 57 + 1 / 1000 : ℚ) : ℝ) (1 - 2 * (7 / 57 + 1 / 1000 : ℚ)) l 6 P :=
  no_kRelaxedStrategy_of_codeSweep (N := 2 ^ 17) (fuel := 400) (e0 := 1 / 1000) (δ := 1 / 2500)
    (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by convert sweep_7_57_plus_k6 using 3; norm_num) hne

end CollatzMoonshot.Benchmark.ArcSolverComputable
