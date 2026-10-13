/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalReturns
import CollatzMoonshot.AmusicalRewireRatio.Restriction

/-! Escape and first-passage infrastructure for the bounded-ratio rewiring. -/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- Uniform upper and lower affine bounds for one forward amusical step. -/
theorem amusical_step_bounds {n : ℤ} (hn : 0 ≤ n) :
    3 * n - 1 ≤ 4 * amusical n ∧ 2 * amusical n ≤ 3 * n := by
  unfold amusical
  split_ifs <;> omega

/-- Uniform upper and lower affine bounds for one backward amusical step. -/
theorem amusicalInv_step_bounds {n : ℤ} (hn : 0 ≤ n) :
    2 * n ≤ 3 * amusicalInv n ∧ 3 * amusicalInv n ≤ 4 * n + 3 := by
  unfold amusicalInv
  split_ifs <;> omega

theorem amusicalNatPerm_step_bounds (n : ℕ) :
    3 * n ≤ 4 * amusicalNatPerm n + 1 ∧ 2 * amusicalNatPerm n ≤ 3 * n := by
  have h := amusical_step_bounds (Int.natCast_nonneg n)
  rw [← amusicalNatPerm_apply_cast] at h
  constructor
  · exact_mod_cast (show 3 * (n : ℤ) ≤ 4 * (amusicalNatPerm n : ℤ) + 1 by omega)
  · exact_mod_cast h.2

theorem amusicalNatPerm_symm_step_bounds (n : ℕ) :
    2 * n ≤ 3 * amusicalNatPerm.symm n ∧
      3 * amusicalNatPerm.symm n ≤ 4 * n + 3 := by
  have h := amusicalInv_step_bounds (Int.natCast_nonneg n)
  rw [← amusicalNatPerm_symm_apply_cast] at h
  exact_mod_cast h

/-- An injective integer-indexed sequence in `ℕ` eventually leaves every bounded interval in
both directions. -/
theorem injective_eventually_abs_gt {f : ℤ → ℕ} (hinj : Function.Injective f) (B : ℕ) :
    ∃ K : ℕ, ∀ j : ℤ, K ≤ j.natAbs → B < f j := by
  have hfinite : (f ⁻¹' Set.Iic B).Finite :=
    (Set.finite_Iic B).preimage hinj.injOn
  obtain ⟨K, hK⟩ := (hfinite.image Int.natAbs).bddAbove
  refine ⟨K + 1, fun j hj ↦ ?_⟩
  by_contra hle
  have hjmem : j ∈ f ⁻¹' Set.Iic B := by
    change f j ≤ B
    omega
  have habs : j.natAbs ≤ K := hK ⟨j, hjmem, rfl⟩
  omega

/-- A natural point on an infinite amusical orbit eventually exceeds every height in both time
directions. -/
theorem amusicalNatPerm_zpow_eventually_gt_of_infinite {x : ℕ}
    (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    ∃ K : ℕ, ∀ j : ℤ, K ≤ j.natAbs → B < (amusicalNatPerm ^ j) x := by
  apply injective_eventually_abs_gt _ B
  intro i j hij
  apply amusicalPerm_zpow_apply_injective_of_infinite hinf
  have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) hij
  simpa using hcast

/-- Both a forward and a backward passage above any prescribed height exist on an infinite
nonnegative amusical orbit. -/
theorem exists_forward_backward_above {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    ∃ p q : ℕ, B < (amusicalNatPerm ^ (p : ℤ)) x ∧
      B < (amusicalNatPerm ^ (-(q : ℤ))) x := by
  obtain ⟨K, hK⟩ := amusicalNatPerm_zpow_eventually_gt_of_infinite hinf B
  refine ⟨K, K, hK K ?_, hK (-K) ?_⟩ <;> simp

theorem exists_forward_above {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    ∃ p : ℕ, B < (amusicalNatPerm ^ (p : ℤ)) x := by
  obtain ⟨p, _, hp, _⟩ := exists_forward_backward_above hinf B
  exact ⟨p, hp⟩

theorem exists_backward_above {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    ∃ q : ℕ, B < (amusicalNatPerm ^ (-(q : ℤ))) x := by
  obtain ⟨_, q, _, hq⟩ := exists_forward_backward_above hinf B
  exact ⟨q, hq⟩

/-- The first nonnegative time at which an infinite orbit passes above `B`. -/
noncomputable def forwardPassage {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) : ℕ :=
  Nat.find (exists_forward_above hinf B)

/-- The first nonpositive time at which an infinite orbit passes above `B`. -/
noncomputable def backwardPassage {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) : ℕ :=
  Nat.find (exists_backward_above hinf B)

theorem forwardPassage_gt {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    B < (amusicalNatPerm ^ (forwardPassage hinf B : ℤ)) x := by
  exact Nat.find_spec (exists_forward_above hinf B)

theorem backwardPassage_gt {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    B < (amusicalNatPerm ^ (-(backwardPassage hinf B : ℤ))) x := by
  exact Nat.find_spec (exists_backward_above hinf B)

theorem forwardPassage_before_le {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B t : ℕ)
    (ht : t < forwardPassage hinf B) :
    (amusicalNatPerm ^ (t : ℤ)) x ≤ B := by
  by_contra hgt
  have hmin : forwardPassage hinf B ≤ t :=
    Nat.find_min' (exists_forward_above hinf B) (by omega)
  omega

theorem backwardPassage_before_le {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B t : ℕ)
    (ht : t < backwardPassage hinf B) :
    (amusicalNatPerm ^ (-(t : ℤ))) x ≤ B := by
  by_contra hgt
  have hmin : backwardPassage hinf B ≤ t :=
    Nat.find_min' (exists_backward_above hinf B) (by omega)
  omega

end CollatzMoonshot.Amusical
