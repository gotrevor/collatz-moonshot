/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycle.Rung

/-!
# Rung predecessors and the near-cycle count (helpers for Theorem NC′)

`IsRungPred n p`: `p < n`, `n` is a forward iterate of `p`, and the forward orbit of `p` never
goes below `n` after time `0`.  So `n` is the minimum of `{Uᵏ p : k ≥ 1}`, which makes the
predecessor injective (`IsRungPred.eq`).

* `exists_isRungPred`: every forward survivor `n ≥ 0` that is not a backward survivor has a
  predecessor `p ≥ 0` (`p = Vᵍ n`, `g` its first backward drop).
* `IsRungPred.le`: every forward survivor `m < n` on the orbit of `n` is `≤ p` (§31's P′).
* `IsRungPred.nearCycleStart`: if `n − p ≤ D`, then `p` is a `D`-near-cycle start.
* `card_fwdSurvivor_le`: with `r` orbits, `#FS ∩ [0, X) ≤ 2r + r ⌊X/D⌋ + #NC_D ∩ [0, X)`.
  The rungs with gap `> D` are `D`-separated on each orbit (by `IsRungPred.le`); this replaces the
  kickoff's multiplicative telescoping by a linear packing.
-/

namespace CollatzMoonshot.Amusical.NearCycle

/-- `p` is the rung predecessor of `n`. -/
def IsRungPred (n p : ℤ) : Prop :=
  p < n ∧ (∃ g : ℕ, amusical^[g] p = n) ∧ ∀ k : ℕ, 1 ≤ k → n ≤ amusical^[k] p

theorem exists_isRungPred {n : ℤ} (hn : FwdSurvivor n) (h0 : 0 ≤ n) (hb : ¬ BwdSurvivor n) :
    ∃ p, 0 ≤ p ∧ IsRungPred n p := by
  classical
  have hex : ∃ t : ℕ, 1 ≤ t ∧ amusicalInv^[t] n < n := by
    unfold BwdSurvivor at hb
    push Not at hb
    obtain ⟨t, h1, h2⟩ := hb
    exact ⟨t, h1, h2⟩
  obtain ⟨-, hdrop⟩ := Nat.find_spec hex
  have hmin : ∀ t, 1 ≤ t → t < Nat.find hex → n ≤ amusicalInv^[t] n := by
    intro t ht1 htk
    by_contra hc
    exact Nat.find_min hex htk ⟨ht1, lt_of_not_ge hc⟩
  refine ⟨_, amusicalInv_iterate_nonneg _ h0, hdrop, ⟨Nat.find hex, ?_⟩, rung_fwd hn hmin⟩
  rw [iterate_rung le_rfl, Nat.sub_self]
  rfl

theorem IsRungPred.eq {n₁ n₂ p : ℤ} (h₁ : IsRungPred n₁ p) (h₂ : IsRungPred n₂ p) : n₁ = n₂ := by
  have key : ∀ {a b : ℤ}, IsRungPred a p → IsRungPred b p → a ≤ b := by
    intro a b ha hb
    obtain ⟨hlt, ⟨g, hg⟩, -⟩ := hb
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · simp at hg; omega
    · exact hg ▸ ha.2.2 g hg0
  exact le_antisymm (key h₁ h₂) (key h₂ h₁)

theorem mem_amusicalOrbit_of_iterate {m n p : ℤ} {g : ℕ} (hm : m ∈ amusicalOrbit n)
    (hg : amusical^[g] p = n) : m ∈ amusicalOrbit p := by
  obtain ⟨j, rfl⟩ := hm
  refine ⟨j + g, ?_⟩
  simp only
  rw [zpow_add, Equiv.Perm.mul_apply, amusicalPerm_pow_nat_apply, hg]

theorem IsRungPred.le {n p m : ℤ} (h : IsRungPred n p) (hm : FwdSurvivor m) (hlt : m < n)
    (horb : m ∈ amusicalOrbit n) : m ≤ p := by
  obtain ⟨-, ⟨g, hg⟩, hfwd⟩ := h
  obtain ⟨t, ht | ht⟩ :=
    Ceiling.exists_iterate_of_mem_amusicalOrbit (mem_amusicalOrbit_of_iterate horb hg)
  · rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp at ht; omega
    · have := hfwd t ht0; omega
  · rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp at ht; omega
    · have hback : amusical^[t] m = p := by
        rw [ht]; exact (Function.LeftInverse.iterate amusical_amusicalInv t) p
      have := hm t ht0
      omega

theorem IsRungPred.nearCycleStart {n p : ℤ} {D : ℕ} (h : IsRungPred n p) (hD : n - p ≤ D) :
    ∃ g ≥ 1, p < amusical^[g] p ∧ amusical^[g] p ≤ p + D ∧
      ∀ k, 1 ≤ k → k < g → p + D < amusical^[k] p := by
  classical
  obtain ⟨hlt, ⟨g, hg⟩, hfwd⟩ := h
  have hex : ∃ k : ℕ, 1 ≤ k ∧ amusical^[k] p ≤ p + D := by
    refine ⟨g, ?_, by omega⟩
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · simp at hg; omega
    · exact hg0
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, h1, ?_, h2, fun k hk1 hk2 => ?_⟩
  · have := hfwd _ h1; omega
  · by_contra hc
    exact Nat.find_min hex hk2 ⟨hk1, le_of_not_gt hc⟩

/-- Two forward and backward survivors on one orbit are equal (each is the orbit minimum). -/
theorem eq_of_survivors {a b : ℤ} (hfa : FwdSurvivor a) (hba : BwdSurvivor a)
    (hfb : FwdSurvivor b) (hbb : BwdSurvivor b) (hab : amusicalOrbit a = amusicalOrbit b) :
    a = b := by
  have key : ∀ {x y : ℤ}, FwdSurvivor x → BwdSurvivor x → y ∈ amusicalOrbit x → x ≤ y := by
    intro x y hfx hbx hy
    obtain ⟨t, ht | ht⟩ := Ceiling.exists_iterate_of_mem_amusicalOrbit hy
    · rcases Nat.eq_zero_or_pos t with rfl | ht0
      · simp at ht; omega
      · exact ht ▸ hfx t ht0
    · rcases Nat.eq_zero_or_pos t with rfl | ht0
      · simp at ht; omega
      · exact ht ▸ hbx t ht0
  have h1 : b ∈ amusicalOrbit a := hab ▸ mem_amusicalOrbit_self b
  have h2 : a ∈ amusicalOrbit b := hab ▸ mem_amusicalOrbit_self a
  exact le_antisymm (key hfa hba h1) (key hfb hbb h2)

open Classical in
/-- **The count.**  With finitely many orbits (`r` of them), forward survivors below `X` number
at most `2r + r ⌊X/D⌋` plus the `D`-near-cycle starts below `X`. -/
theorem card_fwdSurvivor_le (hfin : ¬ AmusicalInfinitelyManyOrbits) :
    ∃ r : ℕ, ∀ D X : ℕ, 1 ≤ D →
      ((Finset.range X).filter fun n : ℕ => FwdSurvivor n).card ≤
        2 * r + r * (X / D) + ((Finset.range X).filter fun p : ℕ =>
          ∃ g ≥ 1, (p : ℤ) < amusical^[g] p ∧ amusical^[g] p ≤ p + D ∧
            ∀ k, 1 ≤ k → k < g → (p : ℤ) + D < amusical^[k] p).card := by
  have hfin' := Set.not_infinite.mp hfin
  refine ⟨hfin'.toFinset.card, fun D X hD => ?_⟩
  set r := hfin'.toFinset.card
  set NC := (Finset.range X).filter fun p : ℕ =>
    ∃ g ≥ 1, (p : ℤ) < amusical^[g] p ∧ amusical^[g] p ≤ p + D ∧
      ∀ k, 1 ≤ k → k < g → (p : ℤ) + D < amusical^[k] p
  set A := (Finset.range X).filter fun n : ℕ => FwdSurvivor n ∧ BwdSurvivor n
  set B := (Finset.range X).filter fun n : ℕ =>
    FwdSurvivor n ∧ ∃ p : ℤ, 0 ≤ p ∧ IsRungPred n p ∧ (n : ℤ) - p ≤ D
  set C := (Finset.range X).filter fun n : ℕ =>
    FwdSurvivor n ∧ ∃ p : ℤ, IsRungPred n p ∧ (D : ℤ) < n - p
  have horbit : ∀ n : ℕ, amusicalOrbit (n : ℤ) ∈ hfin'.toFinset := fun n => by
    rw [Set.Finite.mem_toFinset]; exact ⟨n, by positivity, rfl⟩
  -- the split
  have hsplit : ((Finset.range X).filter fun n : ℕ => FwdSurvivor n) ⊆ A ∪ B ∪ C := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    by_cases hb : BwdSurvivor n
    · exact Or.inl (Or.inl ⟨hn.1, hn.2, hb⟩)
    · obtain ⟨p, hp0, hp⟩ := exists_isRungPred hn.2 (by positivity) hb
      rcases le_or_gt ((n : ℤ) - p) D with h | h
      · exact Or.inl (Or.inr ⟨hn.1, hn.2, p, hp0, hp, h⟩)
      · exact Or.inr ⟨hn.1, hn.2, p, hp, h⟩
  -- orbit minima
  have hA : A.card ≤ r := by
    refine Finset.card_le_card_of_injOn (fun n : ℕ => amusicalOrbit (n : ℤ))
      (fun n _ => horbit n) ?_
    intro a ha b hb hab
    simp only [A, Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
    exact_mod_cast eq_of_survivors ha.2.1 ha.2.2 hb.2.1 hb.2.2 hab
  -- small gaps: the predecessor is a near-cycle start
  have hB : B.card ≤ NC.card := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun (n : ℕ) (q : ℕ) => IsRungPred n q) ?_ ?_
    · intro n hn
      simp only [B, Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨hnX, -, p, hp0, hp, hpD⟩ := hn
      refine ⟨p.toNat, ?_, by rwa [Int.toNat_of_nonneg hp0]⟩
      simp only [NC, Finset.mem_filter, Finset.mem_range]
      have hpn := hp.1
      refine ⟨by omega, ?_⟩
      rw [Int.toNat_of_nonneg hp0]
      exact hp.nearCycleStart hpD
    · intro q _ a ha b hb
      exact_mod_cast ha.2.eq hb.2
  -- large gaps: separated on each orbit
  have hC : C.card ≤ r * (X / D) + r := by
    have h := Finset.card_le_mul_card_image (f := fun n : ℕ => amusicalOrbit (n : ℤ)) C
      (X / D + 1) (by
        intro O _
        refine Ceiling.card_le_of_sep hD (fun n hn => ?_) (fun a ha b hb hab => ?_)
        · simp only [C, Finset.mem_filter, Finset.mem_range] at hn
          exact hn.1.1
        · simp only [C, Finset.mem_filter, Finset.mem_range] at ha hb
          obtain ⟨p, hp, hpD⟩ := hb.1.2.2
          have horb : (a : ℤ) ∈ amusicalOrbit (b : ℤ) := by
            rw [hb.2, ← ha.2]; exact mem_amusicalOrbit_self _
          have := hp.le ha.1.2.1 (by exact_mod_cast hab) horb
          omega)
    have himg : (C.image fun n : ℕ => amusicalOrbit (n : ℤ)) ⊆ hfin'.toFinset := by
      intro O hO
      simp only [Finset.mem_image] at hO
      obtain ⟨n, _, rfl⟩ := hO
      exact horbit n
    calc C.card ≤ (X / D + 1) * (C.image fun n : ℕ => amusicalOrbit (n : ℤ)).card := h
      _ ≤ (X / D + 1) * r := Nat.mul_le_mul_left _ (Finset.card_le_card himg)
      _ = r * (X / D) + r := by ring
  calc _ ≤ (A ∪ B ∪ C).card := Finset.card_le_card hsplit
    _ ≤ A.card + B.card + C.card := by
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        exact Finset.card_union_le _ _
    _ ≤ _ := by omega

end CollatzMoonshot.Amusical.NearCycle
