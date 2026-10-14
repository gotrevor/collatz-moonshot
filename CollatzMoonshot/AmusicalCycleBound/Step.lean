/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalEscape

/-! # Exact arithmetic for one amusical step -/

namespace CollatzMoonshot.Amusical

/-- The additive defect in the cleared-denominator formula for one step of `amusical`. -/
def stepDefect (x : ℤ) : ℤ :=
  2 ^ stepBits x * amusical x - 3 * x

/-- The cleared-denominator identity for one step. -/
theorem stepBits_mul_amusical (x : ℤ) :
    2 ^ stepBits x * amusical x = 3 * x + stepDefect x := by
  simp [stepDefect]

/-- An even step has zero additive defect. -/
theorem stepDefect_eq_zero_of_even {x : ℤ} (hx : x % 2 = 0) : stepDefect x = 0 := by
  unfold stepDefect stepBits amusical
  simp [hx]
  omega

/-- An odd step has additive defect `1` or `-1`, according to its class modulo four. -/
theorem stepDefect_of_odd {x : ℤ} (hx : x % 2 ≠ 0) :
    stepDefect x = if x % 4 = 1 then 1 else -1 := by
  unfold stepDefect stepBits amusical
  simp [hx]
  split_ifs with h4
  · omega
  · omega

/-- Every additive step defect lies in the interval `[-1, 1]`. -/
theorem stepDefect_mem (x : ℤ) : -1 ≤ stepDefect x ∧ stepDefect x ≤ 1 := by
  by_cases hx : x % 2 = 0
  · simp [stepDefect_eq_zero_of_even hx]
  · rw [stepDefect_of_odd hx]
    split <;> omega

/-- The defect vanishes exactly on the even branch. -/
theorem stepDefect_eq_zero_iff (x : ℤ) : stepDefect x = 0 ↔ x % 2 = 0 := by
  constructor
  · intro h
    by_contra hx
    rw [stepDefect_of_odd hx] at h
    split at h <;> omega
  · exact stepDefect_eq_zero_of_even

/-- `stepBits` is one plus the indicator of an odd step. -/
theorem stepBits_eq_one_add_indicator (x : ℤ) :
    stepBits x = 1 + if 2 ∣ x then 0 else 1 := by
  by_cases hx : 2 ∣ x
  · have hx0 : x % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp hx
    simp [stepBits, hx, hx0]
  · have hx0 : x % 2 ≠ 0 := fun h => hx (Int.dvd_iff_emod_eq_zero.mpr h)
    simp [stepBits, hx, hx0]

/-- The total number of halvings is the number of steps plus the number of odd steps. -/
theorem sum_stepBits_eq_add_filter_card (x : ℤ) (p : ℕ) :
    (∑ j ∈ Finset.range p, stepBits (amusical^[j] x)) =
      p + ((Finset.range p).filter fun j => ¬ 2 ∣ amusical^[j] x).card := by
  simp_rw [stepBits_eq_one_add_indicator]
  rw [Finset.sum_add_distrib]
  have hind (j : ℕ) :
      (if 2 ∣ amusical^[j] x then 0 else 1) =
        if ¬ 2 ∣ amusical^[j] x then 1 else 0 := by
    by_cases h : 2 ∣ amusical^[j] x <;> simp [h]
  simp_rw [hind]
  rw [Finset.sum_boole]
  simp

/-- Multiplying consecutive iterates telescopes after adjoining the two endpoints. -/
theorem mul_prod_iterate_succ (f : ℤ → ℤ) (x : ℤ) (p : ℕ) :
    x * ∏ j ∈ Finset.range p, f^[j + 1] x =
      f^[p] x * ∏ j ∈ Finset.range p, f^[j] x := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      rw [Function.iterate_succ_apply']
      calc
        x * ((∏ j ∈ Finset.range p, f^[j + 1] x) * f (f^[p] x)) =
            (x * ∏ j ∈ Finset.range p, f^[j + 1] x) * f (f^[p] x) := by ring
        _ = (f^[p] x * ∏ j ∈ Finset.range p, f^[j] x) * f (f^[p] x) := by rw [ih]
        _ = f (f^[p] x) *
            ((∏ j ∈ Finset.range p, f^[j] x) * f^[p] x) := by ring

/-- On a cycle, shifting every factor in the orbit product leaves the product unchanged. -/
theorem prod_iterate_succ_eq_of_cycle {f : ℤ → ℤ} {x : ℤ} {p : ℕ}
    (hx : x ≠ 0) (hcyc : f^[p] x = x) :
    (∏ j ∈ Finset.range p, f^[j + 1] x) = ∏ j ∈ Finset.range p, f^[j] x := by
  apply mul_left_cancel₀ hx
  rw [mul_prod_iterate_succ, hcyc]

/-- Multiplying all cleared-denominator step identities around a cycle. -/
theorem amusical_cycle_product_identity {x : ℤ} {p : ℕ} (hx : x ≠ 0)
    (hcyc : amusical^[p] x = x) :
    2 ^ (∑ j ∈ Finset.range p, stepBits (amusical^[j] x)) *
        ∏ j ∈ Finset.range p, amusical^[j] x =
      ∏ j ∈ Finset.range p, (3 * amusical^[j] x + stepDefect (amusical^[j] x)) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  rw [← prod_iterate_succ_eq_of_cycle hx hcyc]
  rw [← Finset.prod_mul_distrib]
  simp_rw [Function.iterate_succ_apply', stepBits_mul_amusical]

end CollatzMoonshot.Amusical
