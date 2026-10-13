/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical

/-! The restriction of the amusical permutation to the nonnegative integers. -/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- The amusical permutation preserves the nonnegative integers in both directions. -/
def amusicalNatPerm : Equiv.Perm ℕ where
  toFun n := (amusical n).toNat
  invFun n := (amusicalInv n).toNat
  left_inv n := by
    have hU : 0 ≤ amusical (n : ℤ) := amusical_nonneg (Int.natCast_nonneg n)
    change (amusicalInv ((amusical (n : ℤ)).toNat : ℕ)).toNat = n
    rw [Int.toNat_of_nonneg hU, amusicalInv_amusical]
    simp
  right_inv n := by
    have hV : 0 ≤ amusicalInv (n : ℤ) := amusicalInv_nonneg (Int.natCast_nonneg n)
    change (amusical ((amusicalInv (n : ℤ)).toNat : ℕ)).toNat = n
    rw [Int.toNat_of_nonneg hV, amusical_amusicalInv]
    simp

@[simp] theorem amusicalNatPerm_apply_cast (n : ℕ) :
    (amusicalNatPerm n : ℤ) = amusical n := by
  exact Int.toNat_of_nonneg (amusical_nonneg (Int.natCast_nonneg n))

@[simp] theorem amusicalNatPerm_symm_apply_cast (n : ℕ) :
    (amusicalNatPerm.symm n : ℤ) = amusicalInv n := by
  exact Int.toNat_of_nonneg (amusicalInv_nonneg (Int.natCast_nonneg n))

@[simp] theorem amusicalNatPerm_zpow_apply_cast (j : ℤ) (n : ℕ) :
    ((amusicalNatPerm ^ j) n : ℤ) = (amusicalPerm ^ j) n := by
  revert n
  induction j using Int.induction_on with
  | zero => intro n; simp
  | succ j ih =>
      intro n
      rw [zpow_add_one, zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih,
        amusicalNatPerm_apply_cast]
      rfl
  | pred j ih =>
      intro n
      rw [zpow_sub_one, zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
      congr 1
      exact amusicalNatPerm_symm_apply_cast n

theorem exists_boundedRatio_rewire_of_connected
    (hconnected : ∀ a b : ℕ, (amusicalOrbit a).Infinite →
      (amusicalOrbit b).Infinite → ∃ j : ℤ, (amusicalNatPerm ^ j) a = b) :
    ∃ τ : Equiv.Perm ℕ,
      (∀ n : ℕ, (amusicalOrbit n).Finite → (τ n : ℤ) = amusical n) ∧
      (∃ C : ℕ, ∀ N : ℕ, ((Finset.range N).filter fun n =>
        (τ n : ℤ) ≠ amusical n).card ≤ C * (Nat.log 2 N + 1) ^ 2) ∧
      (∀ n : ℕ, (τ n : ℤ) ≤ 3 * amusical n + 3 ∧
        amusical n ≤ 3 * (τ n : ℤ) + 3) ∧
      ∀ a b : ℕ, (amusicalOrbit a).Infinite → (amusicalOrbit b).Infinite →
        ∃ j : ℤ, (τ ^ j) a = b := by
  refine ⟨amusicalNatPerm, ?_, ⟨0, ?_⟩, ?_, hconnected⟩
  · intro n _
    exact amusicalNatPerm_apply_cast n
  · intro N
    simp
  · intro n
    rw [amusicalNatPerm_apply_cast]
    have hnonneg := amusical_nonneg (Int.natCast_nonneg n)
    constructor <;> omega

/-- If there is at most one infinite nonnegative orbit, no rewiring is necessary. -/
theorem exists_boundedRatio_rewire_of_subsingleton_infiniteOrbits
    (hsub : {O : Set ℤ | ∃ n : ℕ, O = amusicalOrbit n ∧ O.Infinite}.Subsingleton) :
    ∃ τ : Equiv.Perm ℕ,
      (∀ n : ℕ, (amusicalOrbit n).Finite → (τ n : ℤ) = amusical n) ∧
      (∃ C : ℕ, ∀ N : ℕ, ((Finset.range N).filter fun n =>
        (τ n : ℤ) ≠ amusical n).card ≤ C * (Nat.log 2 N + 1) ^ 2) ∧
      (∀ n : ℕ, (τ n : ℤ) ≤ 3 * amusical n + 3 ∧
        amusical n ≤ 3 * (τ n : ℤ) + 3) ∧
      ∀ a b : ℕ, (amusicalOrbit a).Infinite → (amusicalOrbit b).Infinite →
        ∃ j : ℤ, (τ ^ j) a = b := by
  apply exists_boundedRatio_rewire_of_connected
  intro a b ha hb
  have horbit : amusicalOrbit a = amusicalOrbit b := hsub
    ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩
  have hbmem : (b : ℤ) ∈ amusicalOrbit a := horbit.symm ▸ mem_amusicalOrbit_self b
  obtain ⟨j, hj⟩ := hbmem
  refine ⟨j, ?_⟩
  apply Nat.cast_injective (R := ℤ)
  rw [amusicalNatPerm_zpow_apply_cast]
  exact hj

end CollatzMoonshot.Amusical
