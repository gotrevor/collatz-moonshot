/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindow

namespace CollatzMoonshot.Amusical

/-- The exact power of two defining the forward branch cylinder through `n`. -/
def amusicalForwardPeriod : ℕ → ℤ → ℤ
  | 0, _ => 1
  | t + 1, n => (if n % 2 = 0 then 2 else 4) * amusicalForwardPeriod t (amusical n)

theorem amusicalForwardPeriod_pos (t : ℕ) (n : ℤ) : 0 < amusicalForwardPeriod t n := by
  induction t generalizing n with
  | zero => simp [amusicalForwardPeriod]
  | succ t ih =>
      simp only [amusicalForwardPeriod]
      split <;> have := ih (amusical n) <;> omega

/-- Translating by the exact forward-cylinder period preserves the first `t` branches, and
`U^t` turns that translation into multiplication by `3^t`. -/
theorem amusical_iterate_add_forwardPeriod_mul (t : ℕ) (n q : ℤ) :
    amusical^[t] (n + amusicalForwardPeriod t n * q) = amusical^[t] n + 3 ^ t * q := by
  induction t generalizing n q with
  | zero => simp [amusicalForwardPeriod]
  | succ t ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [amusicalForwardPeriod, pow_succ']
      by_cases hn : n % 2 = 0
      · have hnform : n = 2 * (n / 2) := by
          have hdiv := Int.mul_ediv_add_emod n 2
          omega
        have hnimage : amusical n = 3 * (n / 2) := by
          conv_lhs => rw [hnform]
          rw [amusical_two_mul]
        rw [if_pos hn]
        calc
          amusical^[t] (amusical
              (n + 2 * amusicalForwardPeriod t (amusical n) * q)) =
              amusical^[t] (amusical n +
                3 * amusicalForwardPeriod t (amusical n) * q) := by
            congr 1
            rw [show n + 2 * amusicalForwardPeriod t (amusical n) * q =
              2 * (n / 2 + amusicalForwardPeriod t (amusical n) * q) by
                linear_combination hnform]
            rw [amusical_two_mul, hnimage]
            ring
          _ = amusical^[t] (amusical n) + 3 ^ t * (3 * q) := by
            convert ih (amusical n) (3 * q) using 1 <;> ring
          _ = amusical^[t] (amusical n) + 3 * 3 ^ t * q := by ring
      · have hnodd : n % 2 = 1 := by omega
        have hmod : n % 4 = 1 ∨ n % 4 = 3 := by omega
        rw [if_neg hn]
        rcases hmod with hn1 | hn3
        · have hnform : n = 4 * (n / 4) + 1 := by
            have hdiv := Int.mul_ediv_add_emod n 4
            omega
          have hnimage : amusical n = 3 * (n / 4) + 1 := by
            conv_lhs => rw [hnform]
            rw [amusical_four_mul_add_one]
          calc
            amusical^[t] (amusical
                (n + 4 * amusicalForwardPeriod t (amusical n) * q)) =
                amusical^[t] (amusical n +
                  3 * amusicalForwardPeriod t (amusical n) * q) := by
              congr 1
              rw [show n + 4 * amusicalForwardPeriod t (amusical n) * q =
                4 * (n / 4 + amusicalForwardPeriod t (amusical n) * q) + 1 by
                  linear_combination hnform]
              rw [amusical_four_mul_add_one, hnimage]
              ring
            _ = amusical^[t] (amusical n) + 3 ^ t * (3 * q) := by
              convert ih (amusical n) (3 * q) using 1 <;> ring
            _ = amusical^[t] (amusical n) + 3 * 3 ^ t * q := by ring
        · have hnform : n = 4 * (n / 4) + 3 := by
            have hdiv := Int.mul_ediv_add_emod n 4
            omega
          have hnimage : amusical n = 3 * (n / 4) + 2 := by
            conv_lhs => rw [hnform]
            rw [amusical_four_mul_add_three]
          calc
            amusical^[t] (amusical
                (n + 4 * amusicalForwardPeriod t (amusical n) * q)) =
                amusical^[t] (amusical n +
                  3 * amusicalForwardPeriod t (amusical n) * q) := by
              congr 1
              rw [show n + 4 * amusicalForwardPeriod t (amusical n) * q =
                4 * (n / 4 + amusicalForwardPeriod t (amusical n) * q) + 3 by
                  linear_combination hnform]
              rw [amusical_four_mul_add_three, hnimage]
              ring
            _ = amusical^[t] (amusical n) + 3 ^ t * (3 * q) := by
              convert ih (amusical n) (3 * q) using 1 <;> ring
            _ = amusical^[t] (amusical n) + 3 * 3 ^ t * q := by ring

/-- The exact forward-cylinder period is divisible by `2^t`. -/
theorem pow_two_dvd_amusicalForwardPeriod (t : ℕ) (n : ℤ) :
    (2 : ℤ) ^ t ∣ amusicalForwardPeriod t n := by
  induction t generalizing n with
  | zero => simp [amusicalForwardPeriod]
  | succ t ih =>
      simp only [amusicalForwardPeriod, pow_succ]
      obtain ⟨q, hq⟩ := ih (amusical n)
      split
      · exact ⟨q, by rw [hq]; ring⟩
      · exact ⟨2 * q, by rw [hq]; ring⟩

/-- Multiplication by an element coprime to the modulus reaches every residue class. -/
theorem exists_mul_modEq_of_isCoprime {m a d : ℤ} (h : IsCoprime m a) :
    ∃ q : ℤ, a * q ≡ d [ZMOD m] := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨v * d, Int.modEq_iff_dvd.mpr ⟨u * d, ?_⟩⟩
  calc
    d - a * (v * d) = d * 1 - a * (v * d) := by ring
    _ = d * (u * m + v * a) - a * (v * d) := by rw [huv]
    _ = m * (u * d) := by ring

/-- Each forward step loses at most two binary digits of a congruence. -/
theorem amusical_iterate_modEq_two (b t : ℕ) {x y : ℤ}
    (hxy : x ≡ y [ZMOD 2 ^ (b + 2 * t)]) :
    amusical^[t] x ≡ amusical^[t] y [ZMOD 2 ^ b] := by
  rw [Int.modEq_iff_add_fac] at hxy ⊢
  obtain ⟨q, hq⟩ := hxy
  refine ⟨amusicalForwardMultiplier t x * q, ?_⟩
  rw [show y = x + (4 : ℤ) ^ t * ((2 : ℤ) ^ b * q) by
    rw [hq, pow_add]
    rw [show (2 : ℤ) ^ (2 * t) = 4 ^ t by rw [pow_mul]; norm_num]
    ring]
  rw [amusical_iterate_add_pow_four_mul_exact t t le_rfl]
  simp only [Nat.sub_self, pow_zero, one_mul]
  ring

/-- Each backward step loses at most one ternary digit of a congruence. -/
theorem amusicalInv_iterate_modEq_three (b t : ℕ) {x y : ℤ}
    (hxy : x ≡ y [ZMOD 3 ^ (b + t)]) :
    amusicalInv^[t] x ≡ amusicalInv^[t] y [ZMOD 3 ^ b] := by
  rw [Int.modEq_iff_add_fac] at hxy ⊢
  obtain ⟨q, hq⟩ := hxy
  refine ⟨amusicalBackwardMultiplier t x * q, ?_⟩
  rw [show y = x + (3 : ℤ) ^ t * ((3 : ℤ) ^ b * q) by
    rw [hq, pow_add]
    ring]
  rw [amusicalInv_iterate_add_pow_three_mul_exact t t le_rfl]
  simp only [Nat.sub_self, pow_zero, one_mul]
  ring

theorem amusicalInv_iterate_amusical_iterate (t : ℕ) (n : ℤ) :
    amusicalInv^[t] (amusical^[t] n) = n := by
  rw [amusicalInv_iterate_eq_perm_pow, amusical_iterate_eq_perm_pow]
  rw [← Equiv.Perm.mul_apply, ← zpow_add]
  simp

theorem amusical_iterate_amusicalInv_iterate (t : ℕ) (n : ℤ) :
    amusical^[t] (amusicalInv^[t] n) = n := by
  rw [amusical_iterate_eq_perm_pow, amusicalInv_iterate_eq_perm_pow]
  rw [← Equiv.Perm.mul_apply, ← zpow_add]
  simp

end CollatzMoonshot.Amusical
