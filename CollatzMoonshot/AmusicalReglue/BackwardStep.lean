/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalRewireRatio.Restriction

/-! One backward step of the amusical map: `3 V(y) = 2y` at a multiple of `3`, else `4y ± 1`. -/

namespace CollatzMoonshot.Amusical

theorem three_mul_symm_step (y : ℕ) :
    (3 ∣ y → 3 * (amusicalNatPerm.symm y : ℤ) = 2 * y) ∧
    (¬ 3 ∣ y → |3 * (amusicalNatPerm.symm y : ℤ) - 4 * y| ≤ 1) := by
  rw [amusicalNatPerm_symm_apply_cast]
  unfold amusicalInv
  constructor <;> intro h <;> split_ifs <;> (try rw [abs_le]) <;> omega

theorem two_pow_ne_three_pow {w i : ℕ} (hw : 1 ≤ w) : 2 ^ w ≠ 3 ^ i := by
  intro h
  have h2 : 2 ^ w % 2 = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hw
    rw [pow_add]; simp
  have h3 : 3 ^ i % 2 = 1 := by rw [Nat.pow_mod]; simp
  omega

end CollatzMoonshot.Amusical
