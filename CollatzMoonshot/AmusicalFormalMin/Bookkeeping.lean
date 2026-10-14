/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalEscape

namespace CollatzMoonshot.Amusical

theorem amusicalInv_iterate_forward_iterate (x : ℤ) (j i : ℕ) (hi : i ≤ j) :
    amusicalInv^[i] (amusical^[j] x) = amusical^[j - i] x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [show i + k - i = k by omega, Function.iterate_add_apply]
  exact Function.LeftInverse.iterate (f := amusical) (g := amusicalInv) amusicalInv_amusical i _

theorem amusical_iterate_neg (x : ℤ) (j : ℕ) : amusical^[j] (-x) = -(amusical^[j] x) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, amusical_neg]

theorem amusicalInv_neg (x : ℤ) : amusicalInv (-x) = -amusicalInv x := by
  apply amusical_injective
  rw [amusical_amusicalInv, amusical_neg, amusical_amusicalInv]

theorem amusicalInv_iterate_neg (x : ℤ) (j : ℕ) :
    amusicalInv^[j] (-x) = -(amusicalInv^[j] x) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, amusicalInv_neg]

theorem stepBits_neg (x : ℤ) : stepBits (-x) = stepBits x := by
  unfold stepBits
  simp only [Int.neg_emod_two]

end CollatzMoonshot.Amusical
