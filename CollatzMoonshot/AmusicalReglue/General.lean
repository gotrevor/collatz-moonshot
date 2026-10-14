/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalReglue.Blocks

/-!
# Sparse regluing, general form

`exists_reglue_of_gluable`: let `σ` be a permutation of `ℕ` with finitely many periodic points,
every non-periodic point gluable at a set `S` of allowed change points, and infinitely many
gluable `y` with `y, σ⁻¹ y ∈ S`.  Then for any `F, G → ∞` some `π` changes `σ` only at points
of `S`, at `≤ F X` points below `X` (counting changes of `π⁻¹` too), keeps every periodic point,
joins all non-periodic points into one orbit, and has eventually `≤ G X` forward survivors below
`X`.  Theorem Π is `S = univ`; Π′ is `S = odd`.
-/

namespace CollatzMoonshot.Amusical

theorem not_periodic_of_gluePt {σ : Equiv.Perm ℕ} {S : Set ℕ} {x : ℕ} (hx : GluePt σ S x) :
    ¬ ∃ k ≥ 1, (⇑σ)^[k] x = x := by
  rintro ⟨k, hk, hkx⟩
  have hinj := perm_zpow_apply_injective_of_infinite σ hx.1
  have : (σ ^ (k : ℤ)) x = (σ ^ (0 : ℤ)) x := by
    rw [zpow_natCast, Equiv.Perm.coe_pow, hkx]; simp
  have := hinj this
  omega

theorem periodic_apply {σ : Equiv.Perm ℕ} {x : ℕ} (hx : ∃ k ≥ 1, (⇑σ)^[k] x = x) :
    ∃ k ≥ 1, (⇑σ)^[k] (σ x) = σ x := by
  obtain ⟨k, hk, hkx⟩ := hx
  exact ⟨k, hk, by rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hkx]⟩

open Classical in
/-- **Sparse regluing (general form).** -/
theorem exists_reglue_of_gluable (σ : Equiv.Perm ℕ) (S : Set ℕ)
    (hPfin : {x | ∃ k ≥ 1, (⇑σ)^[k] x = x}.Finite)
    (hglue : ∀ x, ¬ (∃ k ≥ 1, (⇑σ)^[k] x = x) → GluePt σ S x)
    (hsp : {y | GluePt σ S y ∧ y ∈ S ∧ σ.symm y ∈ S}.Infinite)
    (F G : ℕ → ℕ) (hF : Filter.Tendsto F .atTop .atTop) (hG : Filter.Tendsto G .atTop .atTop) :
    ∃ π : Equiv.Perm ℕ,
      (∀ x, π x ≠ σ x → x ∈ S) ∧
      (∀ X, ((Finset.range X).filter fun x => π x ≠ σ x ∨ π.symm x ≠ σ.symm x).card ≤ F X) ∧
      (∀ x, (∃ k ≥ 1, (⇑σ)^[k] x = x) → π x = σ x) ∧
      (∀ x y, ¬ (∃ k ≥ 1, (⇑σ)^[k] x = x) → ¬ (∃ k ≥ 1, (⇑σ)^[k] y = y) → π.SameCycle x y) ∧
      (∀ᶠ X in .atTop,
        ((Finset.range X).filter fun m => ∀ t : ℕ, m ≤ (⇑π)^[t] m).card ≤ G X) := by
  have hB (q : ℕ) : ∃ M : ℕ, ∀ N ≥ M, 5 * (q + 1) ≤ F N ∧ 2 * (q + 1) ≤ G N :=
    Filter.eventually_atTop.1 ((Filter.tendsto_atTop.1 hF (5 * (q + 1))).and
      (Filter.tendsto_atTop.1 hG (2 * (q + 1))))
  let B : ℕ → ℕ := fun q => Classical.choose (hB q)
  have hBspec (q N : ℕ) (h : B q ≤ N) : 5 * (q + 1) ≤ F N ∧ 2 * (q + 1) ≤ G N :=
    Classical.choose_spec (hB q) N h
  set hC := rcCuts_isCutSet hsp B
  obtain ⟨φ, hφ, hlater⟩ := exists_wordPerm hsp B
  set π := hC.glueWith φ
  have hspec := spine_spec hsp B
  -- periodic points are never cuts
  have hnotcut {x : ℕ} (hx : ∃ k ≥ 1, (⇑σ)^[k] x = x) : x ∉ rcCuts σ S B := fun h =>
    not_periodic_of_gluePt (rcCuts_gluePt hsp h) hx
  -- where `π` or `π⁻¹` differs from `σ`
  have hchg {x : ℕ} (h : π x ≠ σ x) : σ x ∈ rcCuts σ S B := by
    by_contra hn; exact h (hC.glueWith_apply_of_not_mem φ hn)
  have hchg' {x : ℕ} (h : π.symm x ≠ σ.symm x) : x ∈ rcCuts σ S B := by
    by_contra hn; exact h (hC.glueWith_symm_apply_of_not_mem φ hn)
  refine ⟨π, fun x h => ?_, fun X => ?_, fun x hx => ?_, fun x y hx hy => ?_, ?_⟩
  · rcases hchg h with (⟨n, hn, hnx⟩ | ⟨b, hb⟩) | ⟨_, ⟨b, rfl⟩, hb⟩
    · rw [← σ.injective hnx]; exact (rcChanges_spec hn).1
    · have : x = σ.symm (spine σ S B b) := by rw [hb]; simp
      rw [this]; exact (hspec b).1.2.2
    · rw [← σ.injective hb]; exact (hspec b).1.2.1
  · set m := F X / 5
    have hq {q : ℕ} {v : ℕ} (hv : B q ≤ v) (hvX : v < X) : q ∈ Finset.range m := by
      have := (hBspec q X (by omega)).1
      simp only [Finset.mem_range]; omega
    let T : Finset ℕ := (Finset.range m).image (rcChange σ S B) ∪
      (Finset.range m).image (fun q => σ (rcChange σ S B q)) ∪
      (Finset.range m).image (spine σ S B) ∪
      (Finset.range m).image (fun b => σ (spine σ S B b)) ∪
      (Finset.range m).image (fun b => σ.symm (spine σ S B b))
    have hsub : ((Finset.range X).filter fun x => π x ≠ σ x ∨ π.symm x ≠ σ.symm x) ⊆ T := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      obtain ⟨hxX, hx⟩ := hx
      simp only [T, Finset.mem_union, Finset.mem_image]
      rcases hx with h | h
      · rcases hchg h with (⟨n, ⟨q, hq', rfl⟩, hnx⟩ | ⟨b, hb⟩) | ⟨_, ⟨b, rfl⟩, hb⟩
        · have hx' := σ.injective hnx
          obtain ⟨-, h1, -⟩ := rcChange_spec B q hq'
          exact Or.inl (Or.inl (Or.inl (Or.inl ⟨q, hq h1 (hx' ▸ hxX), hx'⟩)))
        · have hx' : σ.symm (spine σ S B b) = x := by rw [hb]; simp
          exact Or.inr ⟨b, hq (hspec b).2.1 (hx' ▸ hxX), hx'⟩
        · have hx' := σ.injective hb
          exact Or.inl (Or.inl (Or.inr ⟨b, hq (hspec b).2.2.1 (hx' ▸ hxX), hx'⟩))
      · rcases hchg' h with (⟨n, ⟨q, hq', rfl⟩, rfl⟩ | ⟨b, rfl⟩) | ⟨_, ⟨b, rfl⟩, rfl⟩
        · obtain ⟨-, -, h1, -⟩ := rcChange_spec B q hq'
          exact Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq h1 hxX, rfl⟩)))
        · exact Or.inl (Or.inl (Or.inr ⟨b, hq (hspec b).2.2.1 hxX, rfl⟩))
        · exact Or.inl (Or.inr ⟨b, hq (hspec b).2.2.2 hxX, rfl⟩)
    have hT : T.card ≤ 5 * m := by
      refine (Finset.card_union_le _ _).trans ?_
      refine (Nat.add_le_add_right ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
        (Finset.card_union_le _ _) _)) _)) _).trans ?_
      have h1 := (Finset.card_image_le (s := Finset.range m) (f := rcChange σ S B))
      have h2 := (Finset.card_image_le (s := Finset.range m)
        (f := fun q => σ (rcChange σ S B q)))
      have h3 := (Finset.card_image_le (s := Finset.range m) (f := (spine σ S B)))
      have h4 := (Finset.card_image_le (s := Finset.range m)
        (f := fun b => σ (spine σ S B b)))
      have h5 := (Finset.card_image_le (s := Finset.range m)
        (f := fun b => σ.symm (spine σ S B b)))
      simp only [Finset.card_range] at h1 h2 h3 h4 h5
      omega
    calc _ ≤ T.card := Finset.card_le_card hsub
      _ ≤ 5 * m := hT
      _ ≤ F X := by omega
  · exact hC.glueWith_apply_of_not_mem φ (hnotcut (periodic_apply hx))
  · obtain ⟨ka, -, hka⟩ := rcCuts_fwd B (hglue x hx) 0
    obtain ⟨kb, -, hkb⟩ := rcCuts_fwd B (hglue y hy) 0
    exact hC.glueWith_sameCycle φ hφ ⟨ka, hka⟩ ⟨kb, hkb⟩
  · set P := {x | ∃ k ≥ 1, (⇑σ)^[k] x = x}
    have hfin0 := hC.finite_seg_points (spine σ S B 1)
    set Q := {x | ∃ c : rcCuts σ S B, hC.segMin c < spine σ S B 1 ∧
      ∃ r < hC.nextTime c, (σ ^ r) (c : ℕ) = x}
    let K := hPfin.toFinset.card + hfin0.toFinset.card
    filter_upwards [Filter.tendsto_atTop.1 hG (2 * K)] with X hX
    have hsub : ((Finset.range X).filter fun m => ∀ t : ℕ, m ≤ (⇑π)^[t] m) ⊆
        hPfin.toFinset ∪ hfin0.toFinset ∪ (Finset.range (G X / 2)).image (spine σ S B) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      obtain ⟨hxX, hsurv⟩ := hx
      simp only [Finset.mem_union, Set.Finite.mem_toFinset, Finset.mem_image, Finset.mem_range]
      by_cases hper : x ∈ P
      · exact Or.inl (Or.inl hper)
      rcases survivor_mem hsp B φ hlater (hglue x hper) hsurv with h | ⟨b, rfl⟩
      · exact Or.inl (Or.inr h)
      · refine Or.inr ⟨b, ?_, rfl⟩
        have := (hBspec b X (by have := (hspec b).2.2.1; omega)).2
        omega
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ K + G X / 2 := by
        refine (Finset.card_union_le _ _).trans ?_
        have := Finset.card_union_le hPfin.toFinset hfin0.toFinset
        have := Finset.card_image_le (s := Finset.range (G X / 2)) (f := (spine σ S B))
        simp only [Finset.card_range] at this
        omega
      _ ≤ G X := by omega

end CollatzMoonshot.Amusical
