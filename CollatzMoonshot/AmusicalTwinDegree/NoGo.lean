/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalTwinDegree.Frobenius

/-!
# No class-wise Frobenius repair

* `eq_zero_or_one_of_twinU_twinU`: `U² x = x` only for `x ∈ {0, 1}`.  Off the exceptional set the
  two steps must have degree changes summing to `0`, leaving the class pairs `EB, EC, BE, CE, AA`.
  The pair identity `(t^{d₁+d₂} − Q²) x = Q e₁ + t^{d₁} e₂` evaluated at `t = 1` kills the first
  four (the left side vanishes, the right side is `1`), and `AA` reads `(t + 1)² (x − 1) = 0`.
* `no_classwise_core`: the instances `n = 0, t, Q, 1 + t` of a class-wise repair are inconsistent.
  `κ_E ∈ {0, 1}`; then `n = t` fixes `κ_C`, `n = Q` fixes `κ_B`, and `n = 1 + t` fails.
-/

namespace CollatzMoonshot.Amusical.TwinDeg

open Polynomial Function

lemma eval_one_contra (x : (ZMod 2)[X]) (e : (ZMod 2)[X]) (he : e.eval 1 = 1)
    (key : (X ^ 4 - twinQ ^ 2) * x = e) : False := by
  have := congrArg (Polynomial.eval 1) key
  rw [he] at this
  simp [twinQ] at this

/-- `U² x = x` only for `x ∈ {0, 1}`. -/
theorem eq_zero_or_one_of_twinU_twinU (x : (ZMod 2)[X]) (h : twinU (twinU x) = x) :
    x = 0 ∨ x = 1 := by
  by_cases hx : x ∈ exc
  · simp only [exc, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · left; rfl
    · right; rfl
    · exfalso; rw [twinU_X, twinU_Q] at h
      simpa using congrArg (coeff · 0) h
    · exfalso; rw [twinU_X_add_one, twinU_X] at h
      have := congrArg (coeff · 2) h
      simp [twinQ, coeff_X, coeff_one] at this
    · exfalso; rw [twinU_Q, twinU_X_add_one] at h
      have := congrArg (coeff · 0) h
      simp [twinQ, coeff_X, coeff_one] at this
  have hy : twinU x ∉ exc := by rwa [twinU_mem_exc_iff]
  rcases step x hx with ⟨h1, d1⟩ | ⟨h1, d1⟩ | ⟨h1, d1⟩ | ⟨h1, d1⟩ <;>
  rcases step (twinU x) hy with ⟨h2, d2⟩ | ⟨h2, d2⟩ | ⟨h2, d2⟩ | ⟨h2, d2⟩ <;>
  rw [h] at h2 d2 <;>
  try (exfalso; omega)
  · exfalso
    exact eval_one_contra x (X * (X ^ 4 + X ^ 3 + 1)) (by simp; reduce_mod_char)
      (by linear_combination X * h2 + twinQ * h1)
  · exfalso
    exact eval_one_contra x (X * (X ^ 3 + X ^ 2 + 1)) (by simp; reduce_mod_char)
      (by linear_combination X * h2 + twinQ * h1)
  · right
    have key : (X + 1) ^ 2 * (x - 1) = 0 := by
      unfold twinQ at h1 h2
      linear_combination (norm := (ring_nf; reduce_mod_char)) X ^ 2 * h2 + (X ^ 2 + X + 1) * h1
    rcases mul_eq_zero.mp key with h0 | h0
    · exfalso
      simpa using congrArg (Polynomial.eval 0) h0
    · exact sub_eq_zero.mp h0
  · exfalso
    exact eval_one_contra x (twinQ * (X ^ 4 + X ^ 3 + 1)) (by simp [twinQ]; reduce_mod_char)
      (by linear_combination X ^ 3 * h2 + twinQ * h1)
  · exfalso
    exact eval_one_contra x (twinQ * (X ^ 3 + X ^ 2 + 1)) (by simp [twinQ]; reduce_mod_char)
      (by linear_combination X ^ 3 * h2 + twinQ * h1)

/-- Close a polynomial identity over `𝔽₂`. -/
local macro "char2" : tactic =>
  `(tactic| (try unfold twinQ) <;> linear_combination (norm := (ring_nf <;> reduce_mod_char)))

/-- **The no-go core.**  The repair equations at `n = 0, t, Q, 1 + t` are inconsistent. -/
theorem no_classwise_core (k0 k2 k3 : (ZMod 2)[X])
    (h0 : twinU (twinU k0) = k0)
    (hX : twinU (twinU (X ^ 2 + k0)) = twinQ ^ 2 + k3)
    (hQ : twinU (twinU (twinQ ^ 2 + k3)) = (X + 1) ^ 2 + k2)
    (h1X : twinU (twinU ((X + 1) ^ 2 + k2)) = X ^ 2 + k0) : False := by
  rcases eq_zero_or_one_of_twinU_twinU k0 h0 with rfl | rfl
  · rw [add_zero, show (X ^ 2 : (ZMod 2)[X]) = X * X by ring, twinU_E,
      show twinQ * X = X * twinQ by ring, twinU_E] at hX
    obtain rfl : k3 = 0 := by linear_combination -hX
    rw [add_zero, show twinQ ^ 2 = 1 + X ^ 2 * (X ^ 2 + 1) by char2, twinU_A,
      show twinQ * (X ^ 2 + 1) + 1 = X * (X ^ 3 + X ^ 2 + 1) by char2, twinU_E] at hQ
    obtain rfl : k2 = twinQ * (X ^ 3 + X ^ 2 + 1) - (X + 1) ^ 2 := by linear_combination -hQ
    rw [show (X + 1) ^ 2 + (twinQ * (X ^ 3 + X ^ 2 + 1) - (X + 1) ^ 2) = 1 + X + X ^ 3 * X ^ 2
      by char2, twinU_B, show twinQ * X ^ 2 + X = X * (X ^ 3 + X ^ 2 + X + 1) by char2,
      twinU_E] at h1X
    have h : (X ^ 5 + X ^ 3 + 1 : (ZMod 2)[X]) = 0 := by
      have h1X' := h1X; unfold twinQ at h1X'
      linear_combination (norm := (ring_nf <;> reduce_mod_char)) h1X'
    simpa using congrArg (Polynomial.eval 0) h
  · rw [show (X ^ 2 + 1 : (ZMod 2)[X]) = 1 + X ^ 2 * 1 by ring, twinU_A,
      show twinQ * 1 + 1 = X * (X + 1) by char2, twinU_E] at hX
    obtain rfl : k3 = twinQ * (X + 1) - twinQ ^ 2 := by linear_combination -hX
    rw [show twinQ ^ 2 + (twinQ * (X + 1) - twinQ ^ 2) = 1 + X ^ 2 * X by char2, twinU_A,
      show twinQ * X + 1 = 1 + X + X ^ 2 + X ^ 3 * 1 by char2, twinU_C] at hQ
    obtain rfl : k2 = twinQ * 1 + (1 + X) - (X + 1) ^ 2 := by linear_combination -hQ
    rw [show (X + 1) ^ 2 + (twinQ * 1 + (1 + X) - (X + 1) ^ 2) = X * X by char2, twinU_E,
      show twinQ * X = X * twinQ by ring, twinU_E] at h1X
    have h : (X ^ 4 : (ZMod 2)[X]) = 0 := by
      have h1X' := h1X; unfold twinQ at h1X'
      linear_combination (norm := (ring_nf <;> reduce_mod_char)) h1X'
    simpa using congrArg (Polynomial.eval 1) h

end CollatzMoonshot.Amusical.TwinDeg
