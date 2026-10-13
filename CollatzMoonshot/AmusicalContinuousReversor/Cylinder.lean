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

end CollatzMoonshot.Amusical
