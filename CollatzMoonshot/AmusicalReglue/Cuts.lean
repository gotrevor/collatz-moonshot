/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalReglue.Segments
import CollatzMoonshot.AmusicalOddRewire.Glue

/-!
# The cut set of the sparse regluing

Two families of cuts, each indexed so that a cut with index `q` and its neighbours are `≥ B q`:

* **glue cuts** (`rcChanges`): as in GL, index `q = ⟪⟪x, K⟫, side⟫` asks for a change point of
  `S` on the orbit of `x` past time `K` (or before `-K`), here with the change point *and* the cut
  after it `≥ B q`;
* **spine** (`spine`): a strictly increasing sequence of gluable `y` with `y, σ⁻¹ y ∈ S` and
  `σ⁻¹ y, y, σ y ≥ B b`; both `y` and `σ y` are cuts, so `{y}` is a whole segment.
-/

namespace CollatzMoonshot.Amusical

variable {σ : Equiv.Perm ℕ} {S : Set ℕ}

/-- Late `S`-times whose point and successor are both above a value bound. -/
theorem GluePt.exists_fwd2 {x : ℕ} (hx : GluePt σ S x) (B : ℕ) (K : ℤ) :
    ∃ k : ℤ, K ≤ k ∧ B ≤ (σ ^ k) x ∧ B ≤ σ ((σ ^ k) x) ∧ (σ ^ k) x ∈ S := by
  obtain ⟨M, hM⟩ := (finite_orbit_times_le (B := B) hx.1).bddAbove
  obtain ⟨k, hk, hkS⟩ := hx.2.1 (max K (M + 1))
  have hk1 := le_of_max_le_left hk
  have hk2 := le_of_max_le_right hk
  refine ⟨k, hk1, ?_, ?_, hkS⟩
  · by_contra h
    have := hM (show k ∈ {j : ℤ | (σ ^ j) x ≤ B} by simp only [Set.mem_ofPred_eq]; omega)
    omega
  · rw [sigma_zpow_apply]
    by_contra h
    have := hM (show k + 1 ∈ {j : ℤ | (σ ^ j) x ≤ B} by simp only [Set.mem_ofPred_eq]; omega)
    omega

/-- Early `S`-times whose point and successor are both above a value bound. -/
theorem GluePt.exists_bwd2 {x : ℕ} (hx : GluePt σ S x) (B : ℕ) (K : ℤ) :
    ∃ k : ℤ, k ≤ K ∧ B ≤ (σ ^ k) x ∧ B ≤ σ ((σ ^ k) x) ∧ (σ ^ k) x ∈ S := by
  obtain ⟨M, hM⟩ := (finite_orbit_times_le (B := B) hx.1).bddBelow
  obtain ⟨k, hk, hkS⟩ := hx.2.2 (min K (M - 2))
  have hk1 := le_trans hk (min_le_left _ _)
  have hk2 := le_trans hk (min_le_right _ _)
  refine ⟨k, hk1, ?_, ?_, hkS⟩
  · by_contra h
    have := hM (show k ∈ {j : ℤ | (σ ^ j) x ≤ B} by simp only [Set.mem_ofPred_eq]; omega)
    omega
  · rw [sigma_zpow_apply]
    by_contra h
    have := hM (show k + 1 ∈ {j : ℤ | (σ ^ j) x ≤ B} by simp only [Set.mem_ofPred_eq]; omega)
    omega

variable (σ S) in
/-- The glue change point with index `q` (padding `B q` for an invalid index). -/
noncomputable def rcChange (B : ℕ → ℕ) (q : ℕ) : ℕ := by
  classical
  exact
    if h : GluePt σ S (sparseCutSource q) then
      if sparseCutSide q = 0 then
        (σ ^ Classical.choose (h.exists_fwd2 (B q) (sparseCutAfter q))) (sparseCutSource q)
      else
        (σ ^ Classical.choose (h.exists_bwd2 (B q) (-(sparseCutAfter q : ℤ))))
          (sparseCutSource q)
    else B q

theorem rcChange_spec (B : ℕ → ℕ) (q : ℕ) (h : GluePt σ S (sparseCutSource q)) :
    rcChange σ S B q ∈ S ∧ B q ≤ rcChange σ S B q ∧ B q ≤ σ (rcChange σ S B q) ∧
      ∃ k : ℤ, rcChange σ S B q = (σ ^ k) (sparseCutSource q) ∧
        (sparseCutSide q = 0 → (sparseCutAfter q : ℤ) ≤ k) ∧
        (sparseCutSide q ≠ 0 → k ≤ -(sparseCutAfter q : ℤ)) := by
  unfold rcChange
  rw [dif_pos h]
  split_ifs with hs
  · have hc := Classical.choose_spec (h.exists_fwd2 (B q) (sparseCutAfter q))
    exact ⟨hc.2.2.2, hc.2.1, hc.2.2.1, _, rfl, fun _ => hc.1, fun h' => (h' hs).elim⟩
  · have hc := Classical.choose_spec (h.exists_bwd2 (B q) (-(sparseCutAfter q : ℤ)))
    exact ⟨hc.2.2.2, hc.2.1, hc.2.2.1, _, rfl, fun h' => (hs h').elim, fun _ => hc.1⟩

variable (σ S) in
/-- The chosen glue change points. -/
def rcChanges (B : ℕ → ℕ) : Set ℕ :=
  rcChange σ S B '' {q | GluePt σ S (sparseCutSource q)}

theorem rcChanges_spec {B : ℕ → ℕ} {n : ℕ} (hn : n ∈ rcChanges σ S B) :
    n ∈ S ∧ GluePt σ S n := by
  obtain ⟨q, hq, rfl⟩ := hn
  obtain ⟨hS, -, -, k, hk, -⟩ := rcChange_spec B q hq
  exact ⟨hS, hk ▸ hq.zpow k⟩

theorem rcChanges_fwd (B : ℕ → ℕ) {x : ℕ} (hx : GluePt σ S x) (K : ℕ) :
    ∃ k : ℤ, (K : ℤ) ≤ k ∧ (σ ^ k) x ∈ rcChanges σ S B := by
  let q := Nat.pair (Nat.pair x K) 0
  have hsrc : sparseCutSource q = x := by simp [q, sparseCutSource]
  have hq : GluePt σ S (sparseCutSource q) := hsrc ▸ hx
  obtain ⟨-, -, -, k, hk, hK, -⟩ := rcChange_spec B q hq
  refine ⟨k, ?_, ?_⟩
  · simpa [q, sparseCutAfter, sparseCutSide] using hK
  · rw [← hsrc, ← hk]
    exact ⟨q, hq, rfl⟩

theorem rcChanges_bwd (B : ℕ → ℕ) {x : ℕ} (hx : GluePt σ S x) (K : ℕ) :
    ∃ k : ℤ, k ≤ -(K : ℤ) ∧ (σ ^ k) x ∈ rcChanges σ S B := by
  let q := Nat.pair (Nat.pair x K) 1
  have hsrc : sparseCutSource q = x := by simp [q, sparseCutSource]
  have hq : GluePt σ S (sparseCutSource q) := hsrc ▸ hx
  obtain ⟨-, -, -, k, hk, -, hK⟩ := rcChange_spec B q hq
  refine ⟨k, ?_, ?_⟩
  · simpa [q, sparseCutAfter, sparseCutSide] using hK
  · rw [← hsrc, ← hk]
    exact ⟨q, hq, rfl⟩

/-! ### The spine -/

variable (σ S) in
/-- A spine candidate above `M`. -/
noncomputable def spinePick (M : ℕ) : ℕ := by
  classical
  exact if h : ∃ y, (GluePt σ S y ∧ y ∈ S ∧ σ.symm y ∈ S) ∧
      M ≤ σ.symm y ∧ M ≤ y ∧ M ≤ σ y then Classical.choose h else 0

theorem spinePick_spec (hsp : {y | GluePt σ S y ∧ y ∈ S ∧ σ.symm y ∈ S}.Infinite) (M : ℕ) :
    (GluePt σ S (spinePick σ S M) ∧ spinePick σ S M ∈ S ∧ σ.symm (spinePick σ S M) ∈ S) ∧
      M ≤ σ.symm (spinePick σ S M) ∧ M ≤ spinePick σ S M ∧ M ≤ σ (spinePick σ S M) := by
  have hex : ∃ y, (GluePt σ S y ∧ y ∈ S ∧ σ.symm y ∈ S) ∧
      M ≤ σ.symm y ∧ M ≤ y ∧ M ≤ σ y := by
    have hfin : {y | σ.symm y < M ∨ y < M ∨ σ y < M}.Finite := by
      refine ((((Set.finite_lt_nat M).image σ).union (Set.finite_lt_nat M)).union
        ((Set.finite_lt_nat M).image σ.symm)).subset ?_
      intro y hy
      rcases hy with h | h | h
      · exact Or.inl (Or.inl ⟨σ.symm y, h, by simp⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨σ y, h, by simp⟩
    obtain ⟨y, hy, hy'⟩ := (hsp.sdiff hfin).nonempty
    simp only [Set.mem_ofPred_eq, not_or, not_lt] at hy'
    exact ⟨y, hy, hy'⟩
  unfold spinePick
  rw [dif_pos hex]
  exact Classical.choose_spec hex

variable (σ S) in
/-- The spine values: strictly increasing, the `b`-th one `≥ B b` with its neighbours. -/
noncomputable def spine (B : ℕ → ℕ) : ℕ → ℕ
  | 0 => spinePick σ S (B 0)
  | b + 1 => spinePick σ S (max (B (b + 1)) (spine B b + 1))

theorem spine_spec (hsp : {y | GluePt σ S y ∧ y ∈ S ∧ σ.symm y ∈ S}.Infinite) (B : ℕ → ℕ)
    (b : ℕ) :
    (GluePt σ S (spine σ S B b) ∧ spine σ S B b ∈ S ∧ σ.symm (spine σ S B b) ∈ S) ∧
      B b ≤ σ.symm (spine σ S B b) ∧ B b ≤ spine σ S B b ∧ B b ≤ σ (spine σ S B b) := by
  cases b with
  | zero => exact spinePick_spec hsp _
  | succ b =>
      obtain ⟨h1, h2, h3, h4⟩ := spinePick_spec hsp (max (B (b + 1)) (spine σ S B b + 1))
      exact ⟨h1, le_of_max_le_left h2, le_of_max_le_left h3, le_of_max_le_left h4⟩

theorem spine_strictMono (hsp : {y | GluePt σ S y ∧ y ∈ S ∧ σ.symm y ∈ S}.Infinite)
    (B : ℕ → ℕ) : StrictMono (spine σ S B) := by
  refine strictMono_nat_of_lt_succ fun b => ?_
  have := (spinePick_spec hsp (max (B (b + 1)) (spine σ S B b + 1))).2.2.1
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_of_max_le_right this)

/-! ### The cut set -/

variable (σ S) in
/-- The cuts: one step after each glue change point, and each spine point with its successor. -/
def rcCuts (B : ℕ → ℕ) : Set ℕ :=
  σ '' rcChanges σ S B ∪ Set.range (spine σ S B) ∪ σ '' Set.range (spine σ S B)

theorem rcCuts_gluePt (hsp : {y | GluePt σ S y ∧ y ∈ S ∧ σ.symm y ∈ S}.Infinite)
    {B : ℕ → ℕ} {c : ℕ} (hc : c ∈ rcCuts σ S B) : GluePt σ S c := by
  rcases hc with (⟨n, hn, rfl⟩ | ⟨b, rfl⟩) | ⟨_, ⟨b, rfl⟩, rfl⟩
  · simpa only [zpow_one] using (rcChanges_spec hn).2.zpow 1
  · exact (spine_spec hsp B b).1.1
  · simpa only [zpow_one] using (spine_spec hsp B b).1.1.zpow 1

/-- Every gluable point has a cut at some time `≥ K + 1` and some time `≤ -(K - 1)`. -/
theorem rcCuts_fwd (B : ℕ → ℕ) {x : ℕ} (hx : GluePt σ S x) (K : ℕ) :
    ∃ k : ℕ, K < k ∧ (σ ^ (k : ℤ)) x ∈ rcCuts σ S B := by
  obtain ⟨k, hk, hmem⟩ := rcChanges_fwd B hx K
  refine ⟨(k + 1).toNat, by omega, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), ← sigma_zpow_apply]
  exact Or.inl (Or.inl ⟨_, hmem, rfl⟩)

theorem rcCuts_bwd (B : ℕ → ℕ) {x : ℕ} (hx : GluePt σ S x) (K : ℕ) :
    ∃ k : ℕ, K < k ∧ (σ ^ (-(k : ℤ))) x ∈ rcCuts σ S B := by
  obtain ⟨k, hk, hmem⟩ := rcChanges_bwd B hx (K + 2)
  refine ⟨(-(k + 1)).toNat, by omega, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, ← sigma_zpow_apply]
  exact Or.inl (Or.inl ⟨_, hmem, rfl⟩)

theorem rcCuts_isCutSet (hsp : {y | GluePt σ S y ∧ y ∈ S ∧ σ.symm y ∈ S}.Infinite)
    (B : ℕ → ℕ) : IsCutSet σ (rcCuts σ S B) := by
  refine ⟨fun c hc => ?_, fun c hc => ?_, ?_⟩
  · obtain ⟨k, hk, hmem⟩ := rcCuts_fwd B (rcCuts_gluePt hsp hc) 0
    exact ⟨k, hk, hmem⟩
  · obtain ⟨k, hk, hmem⟩ := rcCuts_bwd B (rcCuts_gluePt hsp hc) 0
    exact ⟨k, hk, hmem⟩
  · exact (Set.infinite_range_of_injective (spine_strictMono hsp B).injective).mono
      (fun x hx => Or.inl (Or.inr hx))

end CollatzMoonshot.Amusical
