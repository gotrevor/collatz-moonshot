/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.Bands

/-!
# Auxiliary lemmas for the 3-adic bridge

This module contains the combinatorial and asymptotic helpers used by `Bridge3.lean`.  The
definitions and the three pinned bridge statements remain in that file.
-/

namespace CollatzMoonshot.Conjugacy

open CollatzMoonshot.FrontB

/-- The real parity character, written multiplicatively for reindexing alternating sums. -/
def paritySign (n : ℕ) : ℝ := (-1 : ℝ) ^ n

@[simp] theorem paritySign_add (m n : ℕ) : paritySign (m + n) = paritySign m * paritySign n := by
  simp [paritySign, pow_add]

@[simp] theorem abs_paritySign (n : ℕ) : |paritySign n| = 1 := by
  simp [paritySign]

theorem paritySign_eq_ite (n : ℕ) :
    paritySign n = if n % 2 = 0 then 1 else -1 := by
  simp [paritySign, neg_one_pow_eq_ite, Nat.even_iff]

private theorem three_pow_odd (n : ℕ) : Odd (3 ^ n) := by
  exact (by norm_num : Odd 3).pow

/-- An odd number of alternating lifts through an odd power-of-three modulus leaves exactly the
base parity character. -/
theorem sum_mod_three_pow_mul_paritySign (w : ℕ → ℝ) (m d : ℕ) :
    ∑ y ∈ Finset.range (3 ^ m * 3 ^ d), w (y % 3 ^ m) * paritySign y =
      ∑ c ∈ Finset.range (3 ^ m), w c * paritySign c := by
  induction d with
  | zero =>
    simp only [pow_zero, mul_one]
    exact Finset.sum_congr rfl fun y hy => by
      rw [Nat.mod_eq_of_lt (Finset.mem_range.1 hy)]
  | succ d ih =>
    let K := 3 ^ m * 3 ^ d
    have hKodd : Odd K := (three_pow_odd m).mul (three_pow_odd d)
    have hKmod : K % 3 ^ m = 0 := by
      simp [K, Nat.mul_mod]
    have htotal : 3 ^ m * 3 ^ (d + 1) = (K + K) + K := by
      simp only [pow_succ, K]
      ring
    rw [htotal, Finset.sum_range_add, Finset.sum_range_add]
    have hshift (q y : ℕ) :
        w ((q * K + y) % 3 ^ m) * paritySign (q * K + y) =
          paritySign (q * K) * (w (y % 3 ^ m) * paritySign y) := by
      rw [Nat.add_mod, Nat.mul_mod, hKmod]
      simp only [mul_zero, Nat.zero_mod, zero_add, Nat.mod_mod, paritySign_add]
      ring
    have hshift_one :
        ∑ x ∈ Finset.range K, w ((K + x) % 3 ^ m) * paritySign (K + x) =
          -∑ x ∈ Finset.range K, w (x % 3 ^ m) * paritySign x := by
      rw [Finset.sum_congr rfl (fun y _ => by simpa using hshift 1 y)]
      rw [show paritySign K = (-1 : ℝ) by
        exact hKodd.neg_one_pow]
      simp
    have hshift_two :
        ∑ x ∈ Finset.range K, w (((K + K) + x) % 3 ^ m) * paritySign ((K + K) + x) =
          ∑ x ∈ Finset.range K, w (x % 3 ^ m) * paritySign x := by
      rw [Finset.sum_congr rfl (fun y _ => by
        simpa [two_mul] using hshift 2 y)]
      rw [show paritySign K = (-1 : ℝ) by
        exact hKodd.neg_one_pow]
      simp
    rw [hshift_one, hshift_two]
    convert ih using 1 <;> ring

/-! ## The elementary binomial-tail moment -/

/-- Twice the odd-step count, centered at the depth. -/
def oddDeviation (r j : ℕ) : ℤ := 2 * (oddCount r j : ℤ) - j

/-- Exact second moment of the centered odd-step count over all `j`-bit starts. -/
theorem sum_oddDeviation_sq (j : ℕ) :
    ∑ r ∈ Finset.range (2 ^ j), oddDeviation r j ^ 2 = (j : ℤ) * 2 ^ j := by
  induction j with
  | zero => simp [oddDeviation, oddCount_zero]
  | succ j ih =>
    have hpair (r : ℕ) :
        oddDeviation r (j + 1) ^ 2 + oddDeviation (2 ^ j + r) (j + 1) ^ 2 =
          2 * oddDeviation r j ^ 2 + 2 := by
      rw [oddDeviation, oddDeviation, oddDeviation, oddCount_succ',
        add_comm (2 ^ j) r, oddCount_add_two_pow_succ]
      rcases Nat.mod_two_eq_zero_or_one (tstep^[j] r) with h | h <;>
        simp [h] <;> ring
    rw [pow_succ, mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun r _ => hpair r), Finset.sum_add_distrib,
      ← Finset.mul_sum, ih]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring

theorem sum_oddDeviation_sq_real (j : ℕ) :
    ∑ r ∈ Finset.range (2 ^ j), (oddDeviation r j : ℝ) ^ 2 = (j : ℝ) * 2 ^ j := by
  exact_mod_cast sum_oddDeviation_sq j

/-- The starts whose odd-step count lies outside the mixing band
`j/4 ≤ oddCount r j ≤ 11j/20`. -/
def outOddSet (j : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ j)).filter
    (fun r => 4 * oddCount r j < j ∨ 11 * j / 20 < oddCount r j)

/-- Chebyshev's inequality for both tails outside the mixing band, in a division-free form. -/
theorem outOddSet_card_mul_sq_le (j : ℕ) :
    (outOddSet j).card * (j : ℝ) ^ 2 ≤ 100 * (j : ℝ) * 2 ^ j := by
  have hlarge (r : ℕ) (hr : r ∈ outOddSet j) :
      (j : ℝ) ^ 2 ≤ 100 * (oddDeviation r j : ℝ) ^ 2 := by
    have hj : (0 : ℝ) ≤ j := by positivity
    rcases (Finset.mem_filter.1 hr).2 with hlow | hhigh
    · have hz : (j : ℤ) ≤ -2 * oddDeviation r j := by
        unfold oddDeviation
        omega
      have hz' : (j : ℝ) ≤ -2 * (oddDeviation r j : ℝ) := by exact_mod_cast hz
      nlinarith [sq_nonneg (-2 * (oddDeviation r j : ℝ) - j)]
    · have hz : (j : ℤ) ≤ 10 * oddDeviation r j := by
        unfold oddDeviation
        omega
      have hz' : (j : ℝ) ≤ 10 * (oddDeviation r j : ℝ) := by exact_mod_cast hz
      nlinarith [sq_nonneg ((oddDeviation r j : ℝ) * 10 - j)]
  calc
    (outOddSet j).card * (j : ℝ) ^ 2 =
        ∑ _r ∈ outOddSet j, (j : ℝ) ^ 2 := by simp
    _ ≤ ∑ r ∈ outOddSet j, 100 * (oddDeviation r j : ℝ) ^ 2 := by
      exact Finset.sum_le_sum fun r hr => hlarge r hr
    _ ≤ ∑ r ∈ Finset.range (2 ^ j), 100 * (oddDeviation r j : ℝ) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = 100 * ((j : ℝ) * 2 ^ j) := by
      rw [← Finset.mul_sum, sum_oddDeviation_sq_real]
    _ = 100 * (j : ℝ) * 2 ^ j := by ring

end CollatzMoonshot.Conjugacy
