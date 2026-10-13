/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindow

namespace CollatzMoonshot.Amusical

/-- Equal step symbols put two integers in the same affine branch of `amusical`. -/
theorem stepSym_eq_branch {x y : ℤ}
    (h : (if x % 2 = 0 then (0 : Fin 3) else if x % 4 = 1 then 1 else 2) =
      if y % 2 = 0 then 0 else if y % 4 = 1 then 1 else 2) :
    (x % 2 = 0 ∧ y % 2 = 0) ∨
      (x % 4 = 1 ∧ y % 4 = 1) ∨ (x % 4 = 3 ∧ y % 4 = 3) := by
  split_ifs at h with hx2 hx4 hy2 hy4 <;> simp_all <;> omega

/-- A common forward step-symbol prefix of length `L` fixes the residue modulo `2^L`. -/
theorem pow_two_dvd_sub_of_stepSym_iterate_eq (L : ℕ) (x y : ℤ)
    (h : ∀ i < L,
      (if amusical^[i] x % 2 = 0 then (0 : Fin 3)
        else if amusical^[i] x % 4 = 1 then 1 else 2) =
      if amusical^[i] y % 2 = 0 then 0
        else if amusical^[i] y % 4 = 1 then 1 else 2) :
    (2 : ℤ) ^ L ∣ x - y := by
  induction L generalizing x y with
  | zero => simp
  | succ L ih =>
      have htail : ∀ i < L,
          (if amusical^[i] (amusical x) % 2 = 0 then (0 : Fin 3)
            else if amusical^[i] (amusical x) % 4 = 1 then 1 else 2) =
          if amusical^[i] (amusical y) % 2 = 0 then 0
            else if amusical^[i] (amusical y) % 4 = 1 then 1 else 2 := by
        intro i hi
        rw [← (Function.Commute.self_iterate amusical i).eq x,
          ← (Function.Commute.self_iterate amusical i).eq y]
        simpa only [Function.iterate_succ_apply'] using h (i + 1) (by omega)
      obtain ⟨q, hq⟩ := ih (amusical x) (amusical y) htail
      have hhead := stepSym_eq_branch (h 0 (by omega))
      simp only [Function.iterate_zero_apply] at hhead
      rcases hhead with heven | hone | hthree
      · obtain ⟨a, ha⟩ : ∃ a : ℤ, x = 2 * a := by
          refine ⟨x / 2, ?_⟩
          have hx := Int.mul_ediv_add_emod x 2
          omega
        obtain ⟨b, hb⟩ : ∃ b : ℤ, y = 2 * b := by
          refine ⟨y / 2, ?_⟩
          have hy := Int.mul_ediv_add_emod y 2
          omega
        subst x
        subst y
        rw [amusical_two_mul, amusical_two_mul] at hq
        have hd : (2 : ℤ) ^ L ∣ a - b := by
          have hcop : IsCoprime ((2 : ℤ) ^ L) 3 :=
            (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
          apply hcop.dvd_of_dvd_mul_left
          exact ⟨q, by omega⟩
        obtain ⟨d, hd⟩ := hd
        use d
        rw [pow_succ]
        linear_combination 2 * hd
      · obtain ⟨a, ha⟩ : ∃ a : ℤ, x = 4 * a + 1 := by
          refine ⟨x / 4, ?_⟩
          have hx := Int.mul_ediv_add_emod x 4
          omega
        obtain ⟨b, hb⟩ : ∃ b : ℤ, y = 4 * b + 1 := by
          refine ⟨y / 4, ?_⟩
          have hy := Int.mul_ediv_add_emod y 4
          omega
        subst x
        subst y
        rw [amusical_four_mul_add_one, amusical_four_mul_add_one] at hq
        have hd : (2 : ℤ) ^ L ∣ a - b := by
          have hcop : IsCoprime ((2 : ℤ) ^ L) 3 :=
            (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
          apply hcop.dvd_of_dvd_mul_left
          exact ⟨q, by omega⟩
        obtain ⟨d, hd⟩ := hd
        use 2 * d
        rw [pow_succ]
        linear_combination 4 * hd
      · obtain ⟨a, ha⟩ : ∃ a : ℤ, x = 4 * a + 3 := by
          refine ⟨x / 4, ?_⟩
          have hx := Int.mul_ediv_add_emod x 4
          omega
        obtain ⟨b, hb⟩ : ∃ b : ℤ, y = 4 * b + 3 := by
          refine ⟨y / 4, ?_⟩
          have hy := Int.mul_ediv_add_emod y 4
          omega
        subst x
        subst y
        rw [amusical_four_mul_add_three, amusical_four_mul_add_three] at hq
        have hd : (2 : ℤ) ^ L ∣ a - b := by
          have hcop : IsCoprime ((2 : ℤ) ^ L) 3 :=
            (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
          apply hcop.dvd_of_dvd_mul_left
          exact ⟨q, by omega⟩
        obtain ⟨d, hd⟩ := hd
        use 2 * d
        rw [pow_succ]
        linear_combination 4 * hd

/-- An integer is determined by its complete forward step-symbol itinerary. -/
theorem eq_of_stepSym_iterate_eq (x y : ℤ)
    (h : ∀ i,
      (if amusical^[i] x % 2 = 0 then (0 : Fin 3)
        else if amusical^[i] x % 4 = 1 then 1 else 2) =
      if amusical^[i] y % 2 = 0 then 0
        else if amusical^[i] y % 4 = 1 then 1 else 2) : x = y := by
  let L := (x - y).natAbs
  have hd : (2 : ℤ) ^ L ∣ x - y :=
    pow_two_dvd_sub_of_stepSym_iterate_eq L x y fun i _ => h i
  have hlt : |x - y| < (2 : ℤ) ^ L := by
    rw [← Int.natCast_natAbs]
    change (L : ℤ) < (2 : ℤ) ^ L
    exact_mod_cast (Nat.lt_two_pow_self : L < 2 ^ L)
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd hlt)

end CollatzMoonshot.Amusical
