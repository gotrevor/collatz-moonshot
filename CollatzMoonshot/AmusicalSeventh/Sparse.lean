/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalChains

/-!
# Quantitative infrastructure for sparse sweeping

This file begins the quantitative replacement for the deliberately large `windowBound` used in
`AmusicalWindow`.  The elementary bounds below control every forward and backward affine offset
on a representative modulo `12^L`; they are the first input to the residue-order lemma used by
`sparse_sweep`.
-/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- On the nonnegative integers, one step in either direction is at most `z ↦ 2z+1`. -/
theorem amusical_max_step {z : ℤ} (hz : 0 ≤ z) :
    amusical z ≤ 2 * z + 1 ∧ amusicalInv z ≤ 2 * z + 1 := by
  constructor
  · unfold amusical
    split_ifs <;> omega
  · unfold amusicalInv
    split_ifs <;> omega

/-- Uniform exponential bound for a forward orbit segment starting at a nonnegative integer. -/
theorem amusical_iterate_lt_two_pow_mul {z : ℤ} (hz : 0 ≤ z) (t : ℕ) :
    amusical^[t] z < (2 : ℤ) ^ t * (z + 1) := by
  induction t generalizing z with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply]
      have hz' : 0 ≤ amusical z := amusical_nonneg hz
      have hih := ih hz'
      have hstep := (amusical_max_step hz).1
      rw [pow_succ]
      nlinarith [show (0 : ℤ) < 2 ^ t by positivity]

/-- Uniform exponential bound for a backward orbit segment starting at a nonnegative integer. -/
theorem amusicalInv_iterate_lt_two_pow_mul {z : ℤ} (hz : 0 ≤ z) (t : ℕ) :
    amusicalInv^[t] z < (2 : ℤ) ^ t * (z + 1) := by
  induction t generalizing z with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply]
      have hz' : 0 ≤ amusicalInv z := amusicalInv_nonneg hz
      have hih := ih hz'
      have hstep := (amusical_max_step hz).2
      rw [pow_succ]
      nlinarith [show (0 : ℤ) < 2 ^ t by positivity]

/-- Every length-`L` forward and backward segment from a representative modulo `12^L` stays
below `24^L`.  This explicit bound is what makes window order a finite residue condition at an
exponential threshold. -/
theorem amusical_window_representative_lt {L t c : ℕ} (ht : t ≤ L) (hc : c < 12 ^ L) :
    amusical^[t] (c : ℤ) < 24 ^ L ∧ amusicalInv^[t] (c : ℤ) < 24 ^ L := by
  have hc1 : c + 1 ≤ 12 ^ L := by omega
  have hp : 2 ^ t ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) ht
  have hprod : 2 ^ t * (c + 1) ≤ 24 ^ L := by
    calc
      2 ^ t * (c + 1) ≤ 2 ^ L * 12 ^ L := Nat.mul_le_mul hp hc1
      _ = 24 ^ L := by rw [← Nat.mul_pow]
  constructor
  · exact lt_of_lt_of_le (amusical_iterate_lt_two_pow_mul (Int.natCast_nonneg c) t)
      (by exact_mod_cast hprod)
  · exact lt_of_lt_of_le (amusicalInv_iterate_lt_two_pow_mul (Int.natCast_nonneg c) t)
      (by exact_mod_cast hprod)

end CollatzMoonshot.Amusical
