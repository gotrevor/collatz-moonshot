/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalOddRewire.CutSet

/-!
# The gluing lemma GL

Rewiring a permutation `σ` of `ℕ` only at points of a set `S` fuses into one orbit every infinite
orbit that meets `S` at unboundedly late and unboundedly early times (`GluePt σ S`), and it can be
done changing at most `F N` points below `N`, for any `F → ∞` (`exists_glue`).

Construction: index candidate change points by `q = ⟪⟪x, K⟫, side⟫`; for a gluable source `x`
pick a time `k ≥ K` (forward) or `k ≤ -K` (backward) with `σᵏ x ∈ S` and `σᵏ x ≥ B q + q`,
where `B q` is a threshold past which `F > q`.  The cut set is the `σ`-image of the chosen
points, and `IsCutSet.glue` reconnects at the cuts.
-/

namespace CollatzMoonshot.Amusical

/-- `x` lies on an infinite `σ`-orbit that meets `S` at unboundedly late and early times. -/
def GluePt (σ : Equiv.Perm ℕ) (S : Set ℕ) (x : ℕ) : Prop :=
  (Set.range fun j : ℤ => (σ ^ j) x).Infinite ∧
    (∀ K : ℤ, ∃ k : ℤ, K ≤ k ∧ (σ ^ k) x ∈ S) ∧ ∀ K : ℤ, ∃ k : ℤ, k ≤ K ∧ (σ ^ k) x ∈ S

theorem GluePt.zpow {σ : Equiv.Perm ℕ} {S : Set ℕ} {x : ℕ} (hx : GluePt σ S x) (ε : ℤ) :
    GluePt σ S ((σ ^ ε) x) := by
  obtain ⟨hinf, hf, hb⟩ := hx
  refine ⟨by rwa [perm_zpow_range_apply_zpow], fun K => ?_, fun K => ?_⟩
  · obtain ⟨k, hk, hkS⟩ := hf (K + ε)
    exact ⟨k - ε, by omega, by rwa [perm_zpow_apply_zpow, sub_add_cancel]⟩
  · obtain ⟨k, hk, hkS⟩ := hb (K + ε)
    exact ⟨k - ε, by omega, by rwa [perm_zpow_apply_zpow, sub_add_cancel]⟩

/-- Late `S`-times can be taken above any value bound. -/
theorem GluePt.exists_fwd {σ : Equiv.Perm ℕ} {S : Set ℕ} {x : ℕ} (hx : GluePt σ S x)
    (B : ℕ) (K : ℤ) : ∃ k : ℤ, K ≤ k ∧ B ≤ (σ ^ k) x ∧ (σ ^ k) x ∈ S := by
  obtain ⟨M, hM⟩ := (finite_orbit_times_le (B := B) hx.1).bddAbove
  obtain ⟨k, hk, hkS⟩ := hx.2.1 (max K (M + 1))
  refine ⟨k, le_of_max_le_left hk, ?_, hkS⟩
  by_contra h
  have := hM (show k ∈ {j : ℤ | (σ ^ j) x ≤ B} by simp only [Set.mem_ofPred_eq]; omega)
  have := le_of_max_le_right hk
  omega

/-- Early `S`-times can be taken above any value bound. -/
theorem GluePt.exists_bwd {σ : Equiv.Perm ℕ} {S : Set ℕ} {x : ℕ} (hx : GluePt σ S x)
    (B : ℕ) (K : ℤ) : ∃ k : ℤ, k ≤ K ∧ B ≤ (σ ^ k) x ∧ (σ ^ k) x ∈ S := by
  obtain ⟨M, hM⟩ := (finite_orbit_times_le (B := B) hx.1).bddBelow
  obtain ⟨k, hk, hkS⟩ := hx.2.2 (min K (M - 1))
  refine ⟨k, le_trans hk (min_le_left _ _), ?_, hkS⟩
  by_contra h
  have := hM (show k ∈ {j : ℤ | (σ ^ j) x ≤ B} by simp only [Set.mem_ofPred_eq]; omega)
  have := le_trans hk (min_le_right _ _)
  omega

/-- The candidate change point with index `q`, for the threshold `B`.  For a gluable source it is
a point of `S` on the source's orbit, past time `K` (forward) or before time `-K` (backward). -/
noncomputable def glueChange (σ : Equiv.Perm ℕ) (S : Set ℕ) (B : ℕ → ℕ) (q : ℕ) : ℕ := by
  classical
  exact
    if h : GluePt σ S (sparseCutSource q) then
      if sparseCutSide q = 0 then
        (σ ^ Classical.choose (h.exists_fwd (B q + q) (sparseCutAfter q))) (sparseCutSource q)
      else
        (σ ^ Classical.choose (h.exists_bwd (B q + q) (-(sparseCutAfter q : ℤ))))
          (sparseCutSource q)
    else B q + q

theorem glueChange_ge (σ : Equiv.Perm ℕ) (S : Set ℕ) (B : ℕ → ℕ) (q : ℕ) :
    B q + q ≤ glueChange σ S B q := by
  unfold glueChange
  split_ifs with h hs
  · exact (Classical.choose_spec (h.exists_fwd (B q + q) (sparseCutAfter q))).2.1
  · exact (Classical.choose_spec (h.exists_bwd (B q + q) _)).2.1
  · exact le_rfl

theorem glueChange_spec (σ : Equiv.Perm ℕ) (S : Set ℕ) (B : ℕ → ℕ) (q : ℕ)
    (h : GluePt σ S (sparseCutSource q)) :
    glueChange σ S B q ∈ S ∧ ∃ k : ℤ, glueChange σ S B q = (σ ^ k) (sparseCutSource q) ∧
      (sparseCutSide q = 0 → (sparseCutAfter q : ℤ) ≤ k) ∧
      (sparseCutSide q ≠ 0 → k ≤ -(sparseCutAfter q : ℤ)) := by
  unfold glueChange
  rw [dif_pos h]
  split_ifs with hs
  · have hc := Classical.choose_spec (h.exists_fwd (B q + q) (sparseCutAfter q))
    exact ⟨hc.2.2, _, rfl, fun _ => hc.1, fun h' => (h' hs).elim⟩
  · have hc := Classical.choose_spec (h.exists_bwd (B q + q) (-(sparseCutAfter q : ℤ)))
    exact ⟨hc.2.2, _, rfl, fun h' => (hs h').elim, fun _ => hc.1⟩

/-- The chosen change points. -/
def glueChanges (σ : Equiv.Perm ℕ) (S : Set ℕ) (B : ℕ → ℕ) : Set ℕ :=
  glueChange σ S B '' {q | GluePt σ S (sparseCutSource q)}

theorem glueChanges_spec {σ : Equiv.Perm ℕ} {S : Set ℕ} {B : ℕ → ℕ} {n : ℕ}
    (hn : n ∈ glueChanges σ S B) : n ∈ S ∧ GluePt σ S n := by
  obtain ⟨q, hq, rfl⟩ := hn
  obtain ⟨hS, k, hk, -⟩ := glueChange_spec σ S B q hq
  exact ⟨hS, hk ▸ hq.zpow k⟩

theorem sigma_zpow_apply (σ : Equiv.Perm ℕ) (k : ℤ) (x : ℕ) :
    σ ((σ ^ k) x) = (σ ^ (k + 1)) x := by
  rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]

/-- From a gluable point the chosen changes occur at positive times, negative times, and at the
start of its forward orbit (as cuts, i.e. one step later). -/
theorem glueChanges_fwd {σ : Equiv.Perm ℕ} {S : Set ℕ} (B : ℕ → ℕ) {x : ℕ}
    (hx : GluePt σ S x) (K : ℕ) :
    ∃ k : ℤ, (K : ℤ) ≤ k ∧ (σ ^ k) x ∈ glueChanges σ S B := by
  let q := Nat.pair (Nat.pair x K) 0
  have hsrc : sparseCutSource q = x := by simp [q, sparseCutSource]
  have hq : GluePt σ S (sparseCutSource q) := hsrc ▸ hx
  obtain ⟨-, k, hk, hK, -⟩ := glueChange_spec σ S B q hq
  refine ⟨k, ?_, ?_⟩
  · simpa [q, sparseCutAfter, sparseCutSide] using hK
  · rw [← hsrc, ← hk]
    exact ⟨q, hq, rfl⟩

theorem glueChanges_bwd {σ : Equiv.Perm ℕ} {S : Set ℕ} (B : ℕ → ℕ) {x : ℕ}
    (hx : GluePt σ S x) (K : ℕ) :
    ∃ k : ℤ, k ≤ -(K : ℤ) ∧ (σ ^ k) x ∈ glueChanges σ S B := by
  let q := Nat.pair (Nat.pair x K) 1
  have hsrc : sparseCutSource q = x := by simp [q, sparseCutSource]
  have hq : GluePt σ S (sparseCutSource q) := hsrc ▸ hx
  obtain ⟨-, k, hk, -, hK⟩ := glueChange_spec σ S B q hq
  refine ⟨k, ?_, ?_⟩
  · simpa [q, sparseCutAfter, sparseCutSide] using hK
  · rw [← hsrc, ← hk]
    exact ⟨q, hq, rfl⟩

theorem glueChanges_infinite {σ : Equiv.Perm ℕ} {S : Set ℕ} (B : ℕ → ℕ) {x : ℕ}
    (hx : GluePt σ S x) : (glueChanges σ S B).Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨M, hM⟩ => ?_
  let q := Nat.pair (Nat.pair x (M + 1)) 0
  have hsrc : sparseCutSource q = x := by simp [q, sparseCutSource]
  have hmem : glueChange σ S B q ∈ glueChanges σ S B := ⟨q, show GluePt σ S (sparseCutSource q) from hsrc ▸ hx, rfl⟩
  have h1 := hM hmem
  have h2 := glueChange_ge σ S B q
  have h3 : M + 1 ≤ q := (Nat.right_le_pair _ _).trans (Nat.left_le_pair _ _)
  omega

/-- The cut set: one step after each chosen change point. -/
theorem glueCuts_isCutSet {σ : Equiv.Perm ℕ} {S : Set ℕ} (B : ℕ → ℕ) {x : ℕ}
    (hx : GluePt σ S x) : IsCutSet σ (σ '' glueChanges σ S B) := by
  refine ⟨fun c hc => ?_, fun c hc => ?_, (glueChanges_infinite B hx).image σ.injective.injOn⟩
  · obtain ⟨n, hn, rfl⟩ := hc
    have hgc : GluePt σ S (σ n) := by
      simpa only [zpow_one] using (glueChanges_spec hn).2.zpow 1
    obtain ⟨k, hk, hmem⟩ := glueChanges_fwd B hgc 0
    refine ⟨(k + 1).toNat, by omega, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), ← sigma_zpow_apply]
    exact ⟨_, hmem, rfl⟩
  · obtain ⟨n, hn, rfl⟩ := hc
    have hgc : GluePt σ S (σ n) := by
      simpa only [zpow_one] using (glueChanges_spec hn).2.zpow 1
    obtain ⟨k, hk, hmem⟩ := glueChanges_bwd B hgc 2
    refine ⟨(-(k + 1)).toNat, by omega, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), neg_neg, ← sigma_zpow_apply]
    exact ⟨_, hmem, rfl⟩

/-- **Lemma GL (gluing).**  For any `S` and any `F → ∞` there is a permutation that differs from
`σ` only at gluable points of `S`, at most `F N` times below `N`, and joins all gluable points into
one orbit. -/
theorem exists_glue (σ : Equiv.Perm ℕ) (S : Set ℕ) (F : ℕ → ℕ)
    (hF : Filter.Tendsto F Filter.atTop Filter.atTop) :
    ∃ τ : Equiv.Perm ℕ,
      (∀ n, τ n ≠ σ n → n ∈ S ∧ GluePt σ S n) ∧
      (∀ N, ((Finset.range N).filter fun n => τ n ≠ σ n).card ≤ F N) ∧
      ∀ a b, GluePt σ S a → GluePt σ S b → ∃ j : ℤ, (τ ^ j) a = b := by
  classical
  by_cases hex : ∃ x, GluePt σ S x
  swap
  · refine ⟨σ, fun n h => (h rfl).elim, fun N => by simp, fun a _ ha => (hex ⟨a, ha⟩).elim⟩
  obtain ⟨x, hx⟩ := hex
  have hB (q : ℕ) : ∃ M : ℕ, ∀ N ≥ M, q + 1 ≤ F N :=
    Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hF (q + 1))
  let B : ℕ → ℕ := fun q => Classical.choose (hB q)
  have hBspec (q N : ℕ) (h : B q ≤ N) : q < F N := Classical.choose_spec (hB q) N h
  have hC := glueCuts_isCutSet B hx
  have hchg (n : ℕ) (h : hC.glue n ≠ σ n) : n ∈ glueChanges σ S B := by
    by_contra hn
    exact h (hC.glue_apply_of_not_mem fun ⟨m, hm, hmn⟩ => hn (σ.injective hmn ▸ hm))
  refine ⟨hC.glue, fun n h => glueChanges_spec (hchg n h), fun N => ?_, fun a b ha hb => ?_⟩
  · calc
      _ ≤ ((Finset.range (F N)).image (glueChange σ S B)).card := by
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_range] at hn
        obtain ⟨q, -, rfl⟩ := hchg n hn.2
        have := glueChange_ge σ S B q
        exact Finset.mem_image.2 ⟨q, Finset.mem_range.2 (hBspec q N (by omega)), rfl⟩
      _ ≤ F N := Finset.card_image_le.trans (by simp)
  · have hit {y : ℕ} (hy : GluePt σ S y) : ∃ k : ℕ, (σ ^ (k : ℤ)) y ∈ σ '' glueChanges σ S B := by
      obtain ⟨k, hk, hmem⟩ := glueChanges_fwd B hy 0
      refine ⟨(k + 1).toNat, ?_⟩
      rw [Int.toNat_of_nonneg (by omega), ← sigma_zpow_apply]
      exact ⟨_, hmem, rfl⟩
    exact hC.glue_connects (hit ha) (hit hb)

end CollatzMoonshot.Amusical
