/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalContinuousReversor.Cylinder

namespace CollatzMoonshot.Amusical

/-- Equality of a set with its image under a bijection makes membership invariant. -/
theorem mem_iff_mem_iterate_of_image_eq (f : Equiv.Perm ℤ) (m : ℕ) (S : Set ℤ)
    (h : (f^[m]) '' S = S) (n : ℤ) : n ∈ S ↔ f^[m] n ∈ S := by
  constructor
  · intro hn
    rw [← h]
    exact ⟨n, hn, rfl⟩
  · intro hn
    rw [← h] at hn
    obtain ⟨a, ha, han⟩ := hn
    have : a = n := (f.injective.iterate m) han
    simpa [this] using ha

/-- Membership is consequently invariant under every natural iterate of the bijection. -/
theorem mem_iff_mem_mul_iterate_of_image_eq (f : Equiv.Perm ℤ) (m k : ℕ) (S : Set ℤ)
    (h : (f^[m]) '' S = S) (n : ℤ) : n ∈ S ↔ f^[m * k] n ∈ S := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply]
      exact (mem_iff_mem_iterate_of_image_eq f m S h n).trans (ih (f^[m] n))

/-- On a sufficiently long forward cylinder, one residue modulo a power of two can be sent to
any other residue.  The time can moreover be required to be a multiple of `m`. -/
theorem exists_amusical_mul_iterate_modEq_pow_two (m b : ℕ) (hm : 0 < m) (x y : ℤ) :
    ∃ k : ℕ, ∃ z : ℤ, x ≡ z [ZMOD (2 : ℤ) ^ b] ∧
      amusical^[m * k] z ≡ y [ZMOD (2 : ℤ) ^ b] := by
  let k := b + 1
  let t := m * k
  have hbt : b ≤ t := by
    dsimp [t, k]
    calc
      b ≤ 1 * (b + 1) := by omega
      _ ≤ m * (b + 1) := Nat.mul_le_mul_right _ hm
  have hcop : IsCoprime ((2 : ℤ) ^ b) ((3 : ℤ) ^ t) := by
    exact (by norm_num : IsCoprime (2 : ℤ) 3).pow
  obtain ⟨q, hq⟩ := exists_mul_modEq_of_isCoprime hcop
      (d := y - amusical^[t] x)
  refine ⟨k, x + amusicalForwardPeriod t x * q, ?_, ?_⟩
  · rw [Int.modEq_iff_dvd]
    simpa only [add_sub_cancel_left] using dvd_mul_of_dvd_left
      ((pow_dvd_pow (2 : ℤ) hbt).trans (pow_two_dvd_amusicalForwardPeriod t x)) q
  · change amusical^[t] (x + amusicalForwardPeriod t x * q) ≡ y
        [ZMOD (2 : ℤ) ^ b]
    rw [amusical_iterate_add_forwardPeriod_mul]
    calc
      amusical^[t] x + 3 ^ t * q ≡
          amusical^[t] x + (y - amusical^[t] x) [ZMOD (2 : ℤ) ^ b] :=
        hq.add_left _
      _ = y := by ring

/-- The residue-transitivity target is complete for every power-of-two modulus. -/
theorem amusical_pow_classUnion_invariant_pow_two (m b : ℕ) (hm : 0 < m)
    (R : Set (ZMod (2 ^ b)))
    (h : (amusical^[m]) '' {n : ℤ | (n : ZMod (2 ^ b)) ∈ R} =
      {n : ℤ | (n : ZMod (2 ^ b)) ∈ R}) :
    R = ∅ ∨ R = Set.univ := by
  classical
  by_cases hR : R = ∅
  · exact Or.inl hR
  · right
    obtain ⟨r, hr⟩ := Set.nonempty_iff_ne_empty.mpr hR
    ext s
    simp only [Set.mem_univ, iff_true]
    let x : ℤ := r.cast
    let y : ℤ := s.cast
    obtain ⟨k, z, hxz, hzy⟩ := exists_amusical_mul_iterate_modEq_pow_two m b hm x y
    have hx : (x : ZMod (2 ^ b)) ∈ R := by
      simpa [x] using hr
    have hz : (z : ZMod (2 ^ b)) ∈ R := by
      have heq : (x : ZMod (2 ^ b)) = (z : ZMod (2 ^ b)) :=
        (ZMod.intCast_eq_intCast_iff x z (2 ^ b)).2 hxz
      exact heq ▸ hx
    have hit : (amusical^[m * k] z : ZMod (2 ^ b)) ∈ R :=
      (mem_iff_mem_mul_iterate_of_image_eq amusicalPerm m k _ h z).mp hz
    have heq : (amusical^[m * k] z : ZMod (2 ^ b)) = (y : ZMod (2 ^ b)) :=
      (ZMod.intCast_eq_intCast_iff _ y (2 ^ b)).2 hzy
    have hy : (y : ZMod (2 ^ b)) ∈ R := heq ▸ hit
    simpa [y] using hy

end CollatzMoonshot.Amusical
