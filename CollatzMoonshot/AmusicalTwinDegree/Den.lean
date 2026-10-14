/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalFunctionField
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The twin's cycle denominator `t^{2p} − Q^p` (D1)

For odd `q`, `Q^q` is monic of degree `2q` with next coefficient `q = 1`, so `t^{2q} − Q^q` has
degree exactly `2q − 1`.  Frobenius raises this to the `2^v`-th power.
-/

namespace CollatzMoonshot.Amusical.TwinDeg

open Polynomial

lemma twinQ_monic : twinQ.Monic := FFTwin.fQ_monic

lemma twinQ_natDegree : twinQ.natDegree = 2 := by
  unfold twinQ; compute_degree!

lemma twinQ_nextCoeff : twinQ.nextCoeff = 1 := by
  rw [nextCoeff_of_natDegree_pos (by rw [twinQ_natDegree]; norm_num), twinQ_natDegree]
  unfold twinQ
  simp [coeff_X, coeff_one]

/-- The odd-part denominator: `deg (t^{2q} − Q^q) = 2q − 1` for odd `q`. -/
lemma den_odd_natDegree (q : ℕ) (hq : Odd q) :
    ((X ^ 2 : (ZMod 2)[X]) ^ q - twinQ ^ q).natDegree = 2 * q - 1 := by
  have hq0 : 0 < q := hq.pos
  have hmon : (twinQ ^ q).Monic := twinQ_monic.pow q
  have hdeg : (twinQ ^ q).natDegree = 2 * q := by
    rw [twinQ_monic.natDegree_pow, twinQ_natDegree, mul_comm]
  have hnext : (twinQ ^ q).nextCoeff = 1 := by
    rw [twinQ_monic.nextCoeff_pow, twinQ_nextCoeff, nsmul_eq_mul, mul_one]
    obtain ⟨r, rfl⟩ := hq
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl]; ring
  have hcoef : (twinQ ^ q).coeff (2 * q - 1) = 1 := by
    rw [nextCoeff_of_natDegree_pos (by omega), hdeg] at hnext; exact hnext
  rw [← pow_mul]
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_sub, coeff_X_pow]
    rcases (show N = 2 * q ∨ 2 * q < N by omega) with rfl | hN'
    · rw [if_pos rfl, ← hdeg, hmon.coeff_natDegree, sub_self]
    · rw [if_neg (by omega), coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
  · rw [coeff_sub, coeff_X_pow, if_neg (by omega), hcoef]
    decide

/-- **D1.**  `deg (t^{2p} − Q^p) = 2p − 2^{v₂(p)}`. -/
theorem den_natDegree (p : ℕ) (hp : 0 < p) :
    ((X ^ 2 : (ZMod 2)[X]) ^ p - twinQ ^ p).natDegree = 2 * p - 2 ^ padicValNat 2 p := by
  obtain ⟨v, q, hq, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hp.ne'
  have hq0 : 0 < q := hq.pos
  have hv : padicValNat 2 (2 ^ v * q) = v := by
    rw [padicValNat.mul (by positivity) hq0.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by simpa [Nat.two_dvd_ne_zero] using Nat.odd_iff.mp hq),
      add_zero]
  rw [hv, mul_comm (2 ^ v) q, pow_mul, pow_mul, ← sub_pow_char_pow (p := 2), natDegree_pow,
    den_odd_natDegree q hq]
  have : 1 ≤ q := hq0
  rw [Nat.mul_sub, mul_comm (2 ^ v), mul_one, mul_assoc]

end CollatzMoonshot.Amusical.TwinDeg
