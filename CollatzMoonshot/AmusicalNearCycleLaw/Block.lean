/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycle

/-!
# The block count (helpers for NCU and the LIN corollary)

* `card_fwdSurvivor_block_le_nat`: with `r` orbits, the forward survivors in `(Y, 2Y]` number at
  most `2r + r ⌊(2Y + 1)/D⌋` plus the `D`-near-cycle starts in `(Y, 2Y)`.  A survivor of the block
  is an orbit minimum, or a rung whose predecessor `p` (`NearCycle.IsRungPred`) lies in `(Y, 2Y)`
  with gap `≤ D` (then `p` is a near-cycle start, injectively), or a rung with gap `> D` or
  `p ≤ Y`.  The last kind is `D`-separated on each orbit: for `a < b` on one orbit, `a ≤ p_b`
  (P′), and `p_b ≤ Y < a` is impossible.
-/

namespace CollatzMoonshot.Amusical.NearCycleLaw

open NearCycle

open Classical in
/-- **The block count.** -/
theorem card_fwdSurvivor_block_le_nat (hfin : ¬ AmusicalInfinitelyManyOrbits) :
    ∃ r : ℕ, ∀ Y D : ℕ, 1 ≤ D →
      ((Finset.Ioc Y (2 * Y)).filter fun n : ℕ => FwdSurvivor n).card ≤
        2 * r + r * ((2 * Y + 1) / D) +
          ((Finset.Ioo Y (2 * Y)).filter (NearCycleStart D)).card := by
  have hfin' := Set.not_infinite.mp hfin
  refine ⟨hfin'.toFinset.card, fun Y D hD => ?_⟩
  set r := hfin'.toFinset.card
  set NC := (Finset.Ioo Y (2 * Y)).filter (NearCycleStart D)
  set A := (Finset.Ioc Y (2 * Y)).filter fun n : ℕ => FwdSurvivor n ∧ BwdSurvivor n
  set B := (Finset.Ioc Y (2 * Y)).filter fun n : ℕ =>
    FwdSurvivor n ∧ ∃ p : ℤ, (Y : ℤ) < p ∧ IsRungPred n p ∧ (n : ℤ) - p ≤ D
  set C := (Finset.Ioc Y (2 * Y)).filter fun n : ℕ =>
    FwdSurvivor n ∧ ∃ p : ℤ, IsRungPred n p ∧ ((D : ℤ) < n - p ∨ p ≤ Y)
  have horbit : ∀ n : ℕ, amusicalOrbit (n : ℤ) ∈ hfin'.toFinset := fun n => by
    rw [Set.Finite.mem_toFinset]; exact ⟨n, by positivity, rfl⟩
  -- the split
  have hsplit : ((Finset.Ioc Y (2 * Y)).filter fun n : ℕ => FwdSurvivor n) ⊆ A ∪ B ∪ C := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter]
    by_cases hb : BwdSurvivor n
    · exact Or.inl (Or.inl ⟨hn.1, hn.2, hb⟩)
    · obtain ⟨p, -, hp⟩ := exists_isRungPred hn.2 (by positivity) hb
      by_cases h : (Y : ℤ) < p ∧ (n : ℤ) - p ≤ D
      · exact Or.inl (Or.inr ⟨hn.1, hn.2, p, h.1, hp, h.2⟩)
      · refine Or.inr ⟨hn.1, hn.2, p, hp, ?_⟩
        omega
  -- orbit minima
  have hA : A.card ≤ r := by
    refine Finset.card_le_card_of_injOn (fun n : ℕ => amusicalOrbit (n : ℤ))
      (fun n _ => horbit n) ?_
    intro a ha b hb hab
    simp only [A, Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
    exact_mod_cast eq_of_survivors ha.2.1 ha.2.2 hb.2.1 hb.2.2 hab
  -- small gaps inside the block: the predecessor is a near-cycle start
  have hB : B.card ≤ NC.card := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun (n : ℕ) (q : ℕ) => IsRungPred n q) ?_ ?_
    · intro n hn
      simp only [B, Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨hnY, -, p, hpY, hp, hpD⟩ := hn
      have hp0 : 0 ≤ p := by omega
      refine ⟨p.toNat, ?_, by rwa [Int.toNat_of_nonneg hp0]⟩
      simp only [NC, Finset.mem_filter, Finset.mem_Ioo]
      have hpn := hp.1
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      unfold NearCycleStart
      rw [Int.toNat_of_nonneg hp0]
      exact hp.nearCycleStart hpD
    · intro q _ a ha b hb
      exact_mod_cast ha.2.eq hb.2
  -- the rest: separated on each orbit
  have hC : C.card ≤ r * ((2 * Y + 1) / D) + r := by
    have h := Finset.card_le_mul_card_image (f := fun n : ℕ => amusicalOrbit (n : ℤ)) C
      ((2 * Y + 1) / D + 1) (by
        intro O _
        refine Ceiling.card_le_of_sep hD (fun n hn => ?_) (fun a ha b hb hab => ?_)
        · simp only [C, Finset.mem_filter, Finset.mem_Ioc] at hn
          omega
        · simp only [C, Finset.mem_filter, Finset.mem_Ioc] at ha hb
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
    calc C.card ≤ ((2 * Y + 1) / D + 1) * (C.image fun n : ℕ => amusicalOrbit (n : ℤ)).card := h
      _ ≤ ((2 * Y + 1) / D + 1) * r := Nat.mul_le_mul_left _ (Finset.card_le_card himg)
      _ = r * ((2 * Y + 1) / D) + r := by ring
  calc _ ≤ (A ∪ B ∪ C).card := Finset.card_le_card hsplit
    _ ≤ A.card + B.card + C.card := by
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        exact Finset.card_union_le _ _
    _ ≤ _ := by omega

/-- Near-cycle starts are monotone in `D`: the new return time is the first re-entry of
`[0, p + D']`, which lands above `p` because every earlier time stays above `p + D`. -/
theorem nearCycleStart_mono_aux {D D' p : ℕ} (h : D ≤ D') (hp : NearCycleStart D p) :
    NearCycleStart D' p := by
  classical
  obtain ⟨g, hg1, hgp, hgD, hmin⟩ := hp
  have hex : ∃ k : ℕ, 1 ≤ k ∧ amusical^[k] (p : ℤ) ≤ p + D' := ⟨g, hg1, by push_cast; omega⟩
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, h1, ?_, h2, fun k hk1 hk2 => ?_⟩
  · have hle : Nat.find hex ≤ g := Nat.find_min' hex ⟨hg1, by push_cast; omega⟩
    rcases hle.lt_or_eq with hlt | heq
    · have := hmin _ h1 hlt; omega
    · rw [heq]; exact hgp
  · by_contra hc
    exact Nat.find_min hex hk2 ⟨hk1, le_of_not_gt hc⟩

/-- Under LIN's shape (finite for each `D`, ratio `#NC_D / D` convergent), `#NC_D ≤ K D` for all
`D ≥ 1`: eventually by the limit, and below the threshold by monotonicity. -/
theorem exists_card_nearCycleStart_le
    (hfin : ∀ D : ℕ, {p : ℕ | NearCycleStart D p}.Finite) {κ : ℝ}
    (hκ : Filter.Tendsto (fun D : ℕ => (Nat.card {p : ℕ // NearCycleStart D p} : ℝ) / D)
      Filter.atTop (nhds κ)) :
    ∃ K : ℕ, ∀ D : ℕ, 1 ≤ D → Nat.card {p : ℕ // NearCycleStart D p} ≤ K * D := by
  obtain ⟨D₀, hD₀⟩ := Filter.eventually_atTop.mp
    (hκ.eventually (gt_mem_nhds (show κ < κ + 1 by linarith)))
  refine ⟨max ⌈κ + 1⌉₊ (Nat.card {p : ℕ // NearCycleStart (D₀ + 1) p}), fun D hD => ?_⟩
  rcases le_or_gt (D₀ + 1) D with hle | hlt
  · have h1 := hD₀ D (by omega)
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    rw [div_lt_iff₀ hDpos] at h1
    have h2 : (Nat.card {p : ℕ // NearCycleStart D p} : ℝ) <
        ((max ⌈κ + 1⌉₊ (Nat.card {p : ℕ // NearCycleStart (D₀ + 1) p}) : ℕ) : ℝ) * D := by
      refine h1.trans_le (mul_le_mul_of_nonneg_right ?_ hDpos.le)
      exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
    exact_mod_cast h2.le
  · have hmono : Nat.card {p : ℕ // NearCycleStart D p} ≤
        Nat.card {p : ℕ // NearCycleStart (D₀ + 1) p} :=
      Nat.card_mono (s := {p : ℕ | NearCycleStart D p}) (hfin (D₀ + 1))
        (fun p hp => nearCycleStart_mono_aux hlt.le hp)
    calc _ ≤ Nat.card {p : ℕ // NearCycleStart (D₀ + 1) p} := hmono
      _ ≤ max ⌈κ + 1⌉₊ (Nat.card {p : ℕ // NearCycleStart (D₀ + 1) p}) := le_max_right _ _
      _ ≤ _ := Nat.le_mul_of_pos_right _ hD

open Classical in
/-- The near-cycle starts in a block are among all near-cycle starts. -/
theorem card_nearCycleStart_block_le {D : ℕ} (hfin : {p : ℕ | NearCycleStart D p}.Finite)
    (Y : ℕ) : ((Finset.Ioo Y (2 * Y)).filter (NearCycleStart D)).card ≤
      Nat.card {p : ℕ // NearCycleStart D p} := by
  have h := Nat.card_mono (s := (((Finset.Ioo Y (2 * Y)).filter (NearCycleStart D) : Finset ℕ) :
    Set ℕ)) hfin (fun p hp => by simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp; exact hp.2)
  refine le_of_eq_of_le ?_ h
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]

end CollatzMoonshot.Amusical.NearCycleLaw
