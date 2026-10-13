/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical

/-!
# Infrastructure for sparsely rewiring infinite permutation orbits

The lemmas here isolate the properness and annulus-crossing facts used by the construction in
`rewire_single_orbit`.
-/

namespace CollatzMoonshot.Amusical

/-- The integer parametrization of an infinite orbit of a permutation has no repetitions. -/
theorem perm_zpow_apply_injective_of_infinite {α : Type*} (σ : Equiv.Perm α) {x : α}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) :
    Function.Injective fun j : ℤ => (σ ^ j) x := by
  by_contra h
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, heq, hij⟩ := h
  have hfix : (σ ^ (i - j)) x = x := by
    apply (σ ^ j).injective
    rw [← Equiv.Perm.mul_apply, ← zpow_add, show j + (i - j) = i by omega]
    simpa using heq
  let p := (i - j).natAbs
  have hp : 0 < p := Int.natAbs_pos.mpr (sub_ne_zero.mpr hij)
  have hperiod : (σ ^ (p : ℤ)) x = x := by
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hij).symm with hpos | hneg
    · simpa only [p, Int.natCast_natAbs, abs_of_pos hpos] using hfix
    · have hfixneg : (σ ^ (-(i - j))) x = x := by
        apply (σ ^ (i - j)).injective
        rw [← Equiv.Perm.mul_apply, ← zpow_add]
        simp [hfix]
      simpa only [p, Int.natCast_natAbs, abs_of_neg hneg] using hfixneg
  have hper : Function.IsPeriodicPt (fun y => σ • y) p x := by
    change (⇑σ)^[p] x = x
    rw [← Equiv.Perm.coe_pow]
    exact hperiod
  have hmin : 0 < Function.minimalPeriod (fun y => σ • y) x :=
    hper.minimalPeriod_pos hp
  letI : NeZero (Function.minimalPeriod (fun y => σ • y) x) := ⟨hmin.ne'⟩
  have horbit : (MulAction.orbit (Subgroup.zpowers σ) x).Finite := by
    rw [← Set.finite_coe_iff]
    exact (MulAction.orbitZPowersEquiv σ x).finite_iff.mpr inferInstance
  apply hinf
  convert horbit using 1
  ext y
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨σ ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨k, rfl⟩

/-- An infinite permutation orbit visits a bounded set at only finitely many integer times. -/
theorem finite_orbit_times_le {σ : Equiv.Perm ℕ} {x B : ℕ}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) :
    {j : ℤ | (σ ^ j) x ≤ B}.Finite := by
  have hinj := perm_zpow_apply_injective_of_infinite σ hinf
  exact (Set.finite_le_nat B).preimage hinj.injOn

/-- Both forward and backward halves of an infinite permutation orbit are unbounded. -/
theorem exists_nat_iterate_gt {σ : Equiv.Perm ℕ} {x : ℕ}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) (B : ℕ) :
    (∃ k : ℕ, B < (σ ^ (k : ℤ)) x) ∧ (∃ k : ℕ, B < (σ ^ (-(k : ℤ))) x) := by
  have hinj := perm_zpow_apply_injective_of_infinite σ hinf
  constructor
  · by_contra h
    push Not at h
    have hrange : (Set.range fun k : ℕ => (σ ^ (k : ℤ)) x).Finite :=
      (Set.finite_le_nat B).subset (Set.range_subset_iff.mpr h)
    exact Set.infinite_range_of_injective
      (hinj.comp Int.ofNat_injective) hrange
  · by_contra h
    push Not at h
    have hrange : (Set.range fun k : ℕ => (σ ^ (-(k : ℤ))) x).Finite :=
      (Set.finite_le_nat B).subset (Set.range_subset_iff.mpr h)
    apply Set.infinite_range_of_injective _ hrange
    exact hinj.comp fun a b hab => by simpa using congrArg Int.natAbs hab

/-- A doubling-bounded permutation orbit crosses every sufficiently high annulus in both time
directions.  This is the quantitative input that lets the eventual cuts be chosen sparsely. -/
theorem exists_forward_backward_mem_Ico {σ : Equiv.Perm ℕ}
    (hstep : ∀ n, σ n ≤ 2 * n + 1 ∧ σ.symm n ≤ 2 * n + 1) {x Y : ℕ}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) (hxY : x < Y) :
    (∃ k : ℕ, (σ ^ k) x ∈ Set.Ico Y (2 * Y)) ∧
      ∃ k : ℕ, (σ.symm ^ k) x ∈ Set.Ico Y (2 * Y) := by
  have cross (π : Equiv.Perm ℕ) (hπ : ∀ n, π n ≤ 2 * n + 1)
      (hunbounded : ∃ k : ℕ, Y ≤ (π ^ k) x) :
      ∃ k : ℕ, (π ^ k) x ∈ Set.Ico Y (2 * Y) := by
    let k := Nat.find hunbounded
    have hkY : Y ≤ (π ^ k) x := Nat.find_spec hunbounded
    have hkpos : 0 < k := by
      by_contra hk
      have : k = 0 := Nat.eq_zero_of_not_pos hk
      rw [this] at hkY
      exact (Nat.not_le_of_lt hxY) hkY
    obtain ⟨l, hlk⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
    rw [hlk] at hkY
    have hl : (π ^ l) x < Y := by
      by_contra hlt
      have hle : Y ≤ (π ^ l) x := le_of_not_gt hlt
      have := Nat.find_min' hunbounded hle
      omega
    have hlt : (π ^ (l + 1)) x < 2 * Y := by
      rw [pow_succ', Equiv.Perm.mul_apply]
      have := hπ ((π ^ l) x)
      omega
    exact ⟨l + 1, hkY, hlt⟩
  constructor
  · apply cross σ (fun n => (hstep n).1)
    obtain ⟨k, hk⟩ := (exists_nat_iterate_gt hinf Y).1
    exact ⟨k, by simpa [zpow_natCast] using hk.le⟩
  · apply cross σ.symm (fun n => (hstep n).2)
    obtain ⟨k, hk⟩ := (exists_nat_iterate_gt hinf Y).2
    refine ⟨k, ?_⟩
    rw [zpow_neg, zpow_natCast] at hk
    change Y ≤ (σ⁻¹ ^ k) x
    simpa only [inv_pow] using hk.le

end CollatzMoonshot.Amusical
