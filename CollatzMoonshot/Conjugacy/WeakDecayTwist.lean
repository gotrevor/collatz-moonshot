/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.WeakDecayAux

/-!
# Twisted Fourier inversion for C1⁺

This file carries out the per-slice Fourier inversion in the reduction from
`OverPrecSliceCharDecay` to `WeakDecayOnZ3`.  The coefficient is the Fourier transform, on
`ZMod (3^a)`, of least-residue parity twisted by the start frequency at the finer modulus
`3^(a+k)`.
-/

namespace CollatzMoonshot.Conjugacy

open CollatzMoonshot.FrontB

/-- Least-residue parity with the extra start-frequency phase, regarded as a function on
`ZMod (3^a)`. -/
noncomputable def twistedParity (m a k : ℕ) (η : ZMod (3 ^ k))
    (y : ZMod (3 ^ a)) : ℂ :=
  (paritySign y.val : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I *
      (((η.val * 2 ^ m * y.val : ℕ) : ℂ) / (3 ^ (a + k) : ℂ)))

/-- The normalized Fourier coefficient of `twistedParity`. -/
noncomputable def twistedHat (m a k : ℕ) (η : ZMod (3 ^ k))
    (ξ : ZMod (3 ^ a)) : ℂ :=
  ((3 ^ a : ℕ) : ℂ)⁻¹ * ∑ z : ZMod (3 ^ a),
    twistedParity m a k η z * ZMod.stdAddChar (- (ξ * z))

/-- Fourier inversion for the twisted least-residue parity function. -/
theorem twistedParity_eq_fourier (m a k : ℕ) (η : ZMod (3 ^ k))
    (y : ZMod (3 ^ a)) :
    twistedParity m a k η y =
      ∑ ξ : ZMod (3 ^ a), twistedHat m a k η ξ * ZMod.stdAddChar (ξ * y) := by
  simpa [twistedHat] using
    (zmod_fourier_inversion a (twistedParity m a k η) y).symm

/-- The standard character at a natural multiple has the expected exponential form. -/
theorem stdAddChar_mul_natCast_eq_exp (k r : ℕ) (η : ZMod (3 ^ k)) :
    ZMod.stdAddChar (η * (r : ZMod (3 ^ k))) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((η.val * r : ℕ) : ℂ) / (3 ^ k : ℂ))) := by
  have heta : η * (r : ZMod (3 ^ k)) =
      ((η.val * r : ℕ) : ZMod (3 ^ k)) := by
    calc
      η * (r : ZMod (3 ^ k)) =
          (η.val : ZMod (3 ^ k)) * (r : ZMod (3 ^ k)) := by
            rw [ZMod.natCast_zmod_val]
      _ = ((η.val * r : ℕ) : ZMod (3 ^ k)) := by norm_cast
  rw [heta]
  have h := ZMod.stdAddChar_coe (N := 3 ^ k) (η.val * r : ℤ)
  convert h using 1 <;> push_cast <;> ring_nf

/-- Raising the modulus from `3^a` to `3^(a+k)` multiplies a frequency by `3^k`. -/
theorem stdAddChar_lift_three_pow (a k n : ℕ) (ξ : ZMod (3 ^ a)) :
    ZMod.stdAddChar (ξ * (n : ZMod (3 ^ a))) =
      ZMod.stdAddChar (((3 ^ k * ξ.val : ℕ) : ZMod (3 ^ (a + k))) *
        (n : ZMod (3 ^ (a + k)))) := by
  rw [stdAddChar_mul_natCast_eq_exp a n ξ]
  rw [show ((3 ^ k * ξ.val : ℕ) : ZMod (3 ^ (a + k))) *
      (n : ZMod (3 ^ (a + k))) =
        ((3 ^ k * ξ.val * n : ℕ) : ZMod (3 ^ (a + k))) by norm_cast]
  rw [show ((3 ^ k * ξ.val * n : ℕ) : ZMod (3 ^ (a + k))) =
      ((3 ^ k * ξ.val * n : ℤ) : ZMod (3 ^ (a + k))) by norm_cast]
  rw [ZMod.stdAddChar_coe]
  push_cast
  rw [pow_add]
  field_simp

/-- A negative natural frequency in exponential notation is the corresponding standard
additive character. -/
theorem exp_neg_nat_eq_stdAddChar (A n : ℕ) :
    Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℂ) / (3 ^ A : ℂ)))) =
      ZMod.stdAddChar ((-(n : ℤ)) : ZMod (3 ^ A)) := by
  have h := ZMod.stdAddChar_coe (N := 3 ^ A) (-(n : ℤ))
  convert h.symm using 1 <;> push_cast <;> ring_nf

/-- The standard character of a natural representative, without reducing it to `ZMod.val`. -/
theorem stdAddChar_nat_eq_exp (A n : ℕ) :
    ZMod.stdAddChar (n : ZMod (3 ^ A)) =
      Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) / (3 ^ A : ℂ))) := by
  have h := ZMod.stdAddChar_coe (N := 3 ^ A) (n : ℤ)
  convert h using 1 <;> push_cast <;> ring_nf

/-- The fine-modulus frequency produced after reindexing Fourier inversion by multiplication
with the unit `2^m`. -/
def overPrecFrequencyZMod (a k : ℕ) (η : ZMod (3 ^ k)) (ξ : ZMod (3 ^ a)) :
    ZMod (3 ^ (a + k)) :=
  (3 ^ k * ξ.val : ℕ) - η.val

/-- A nonnegative representative of `overPrecFrequencyZMod`.  Adding one copy of the fine
modulus makes the later exact `3`-adic factorization an equality in `ℕ`. -/
def overPrecFrequencyNat (a k : ℕ) (η : ZMod (3 ^ k)) (ξ : ZMod (3 ^ a)) : ℕ :=
  3 ^ (a + k) + 3 ^ k * ξ.val - η.val

/-- The unit frequency left after removing the exact `3`-power in a nonzero start frequency. -/
def overPrecFrequencyUnit (a k : ℕ) (η : ZMod (3 ^ k)) (ξ : ZMod (3 ^ a)) : ℕ :=
  let v := padicValNat 3 η.val
  3 ^ (a + (k - v)) + 3 ^ (k - v) * ξ.val - η.val.divMaxPow 3

/-- The natural fine frequency has exactly the `3`-power of the nonzero start frequency:
it factors by `3^v`, the remaining precision is positive, and the quotient is prime to `3`. -/
theorem overPrecFrequencyNat_normalize {a k : ℕ} {η : ZMod (3 ^ k)}
    (ξ : ZMod (3 ^ a)) (hη : η ≠ 0) :
    let v := padicValNat 3 η.val
    v < k ∧
      overPrecFrequencyNat a k η ξ = 3 ^ v * overPrecFrequencyUnit a k η ξ ∧
      ¬ 3 ∣ overPrecFrequencyUnit a k η ξ := by
  let v := padicValNat 3 η.val
  let u := η.val.divMaxPow 3
  have hηval : η.val ≠ 0 := by
    intro h
    apply hη
    apply ZMod.val_injective
    simp [h]
  have hfac : 3 ^ v * u = η.val := by
    exact Nat.pow_padicValNat_mul_divMaxPow 3 η.val
  have hvk : v < k := by
    by_contra hnot
    have hkv : k ≤ v := Nat.le_of_not_gt hnot
    have hdvd : 3 ^ k ∣ η.val :=
      (Nat.pow_dvd_pow 3 hkv).trans pow_padicValNat_dvd
    have hge : 3 ^ k ≤ η.val := Nat.le_of_dvd (Nat.pos_of_ne_zero hηval) hdvd
    exact (Nat.not_le_of_lt η.val_lt) hge
  have hu : ¬ 3 ∣ u := Nat.not_dvd_divMaxPow (by norm_num) hηval
  have hmul_lt : 3 ^ v * u < 3 ^ v * 3 ^ (k - v) := by
    calc
      3 ^ v * u = η.val := hfac
      _ < 3 ^ k := η.val_lt
      _ = 3 ^ v * 3 ^ (k - v) := by
        rw [← pow_add, Nat.add_sub_of_le hvk.le]
  have hult : u < 3 ^ (k - v) := Nat.lt_of_mul_lt_mul_left hmul_lt
  let q := 3 ^ (a + (k - v)) + 3 ^ (k - v) * ξ.val - u
  have hbpos : 0 < k - v := Nat.sub_pos_of_lt hvk
  have hsmall : 3 ^ (k - v) ≤ 3 ^ (a + (k - v)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have huq : u ≤ 3 ^ (a + (k - v)) + 3 ^ (k - v) * ξ.val := by
    exact le_trans hult.le (le_trans hsmall (Nat.le_add_right _ _))
  have hqadd : u + q = 3 ^ (a + (k - v)) + 3 ^ (k - v) * ξ.val := by
    dsimp [q]
    exact Nat.add_sub_of_le huq
  have hq_unit : ¬ 3 ∣ q := by
    intro hq
    apply hu
    apply (Nat.dvd_add_iff_right hq).mpr
    rw [add_comm, hqadd]
    have hd1 : 3 ∣ 3 ^ (a + (k - v)) :=
      dvd_pow_self 3 (show a + (k - v) ≠ 0 by omega)
    have hd2 : 3 ∣ 3 ^ (k - v) * ξ.val :=
      (dvd_pow_self 3 (show k - v ≠ 0 by omega)).mul_right ξ.val
    exact Nat.dvd_add hd1 hd2
  refine ⟨hvk, ?_, ?_⟩
  · unfold overPrecFrequencyNat overPrecFrequencyUnit
    change 3 ^ (a + k) + 3 ^ k * ξ.val - η.val =
      3 ^ v * (3 ^ (a + (k - v)) + 3 ^ (k - v) * ξ.val - u)
    have hexp1 : a + k = v + (a + (k - v)) := by omega
    have hexp2 : k = v + (k - v) := by omega
    have hp1 : 3 ^ (a + k) = 3 ^ v * 3 ^ (a + (k - v)) :=
      (congrArg (fun e : ℕ => 3 ^ e) hexp1).trans (pow_add 3 v (a + (k - v)))
    have hp2 : 3 ^ k = 3 ^ v * 3 ^ (k - v) :=
      (congrArg (fun e : ℕ => 3 ^ e) hexp2).trans (pow_add 3 v (k - v))
    have hbase : 3 ^ (a + k) + 3 ^ k * ξ.val =
        3 ^ v * (3 ^ (a + (k - v)) + 3 ^ (k - v) * ξ.val) := by
      calc
        _ = 3 ^ v * 3 ^ (a + (k - v)) +
              (3 ^ v * 3 ^ (k - v)) * ξ.val :=
          congrArg₂ (fun x y : ℕ => x + y * ξ.val) hp1 hp2
        _ = _ := by ring
    calc
      _ = 3 ^ v * (3 ^ (a + (k - v)) + 3 ^ (k - v) * ξ.val) -
          3 ^ v * u := congrArg₂ Nat.sub hbase hfac.symm
      _ = _ := by rw [Nat.mul_sub_left_distrib]
  · simpa [overPrecFrequencyUnit, v, u, q] using hq_unit

/-- The chosen natural representative denotes the fine cyclic-group frequency. -/
theorem overPrecFrequencyNat_cast (a k : ℕ) (η : ZMod (3 ^ k)) (ξ : ZMod (3 ^ a)) :
    (overPrecFrequencyNat a k η ξ : ZMod (3 ^ (a + k))) =
      overPrecFrequencyZMod a k η ξ := by
  have hpow : 3 ^ k ≤ 3 ^ (a + k) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have heta : η.val ≤ 3 ^ (a + k) + 3 ^ k * ξ.val := by
    exact le_trans η.val_lt.le (le_trans hpow (Nat.le_add_right _ _))
  unfold overPrecFrequencyNat overPrecFrequencyZMod
  rw [Nat.cast_sub heta, Nat.cast_add, Nat.cast_mul]
  have hmod : ((3 ^ (a + k) : ℕ) : ZMod (3 ^ (a + k))) = 0 := ZMod.natCast_self _
  rw [hmod, zero_add]

/-- A single reindexed Fourier term is exactly the additive character of the iterate numerator
at the finer modulus. -/
theorem twistedNumerator_term_eq {m a k r : ℕ} (η : ZMod (3 ^ k))
    (ξ : ZMod (3 ^ a)) (ha : oddCount r m = a) :
    ZMod.stdAddChar (((2 ^ m : ℕ) : ZMod (3 ^ a)) * ξ *
        (tstep^[m] r : ZMod (3 ^ a))) *
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((η.val * (2 ^ m * tstep^[m] r - 3 ^ a * r) : ℕ) : ℂ) /
          (3 ^ (a + k) : ℂ)))) =
    ZMod.stdAddChar (overPrecFrequencyZMod a k η ξ *
      ((2 ^ m * tstep^[m] r - 3 ^ a * r : ℕ) : ZMod (3 ^ (a + k)))) := by
  let N := 2 ^ m * tstep^[m] r - 3 ^ a * r
  have hle := three_pow_mul_le_two_pow_iterate ha
  have hsub : 3 ^ a * r + N = 2 ^ m * tstep^[m] r := by
    dsimp [N]
    exact Nat.add_sub_of_le hle
  have hiter :
      ((2 ^ m : ℕ) : ZMod (3 ^ a)) * (tstep^[m] r : ZMod (3 ^ a)) =
        (N : ZMod (3 ^ a)) := by
    have hc := congrArg (fun n : ℕ => (n : ZMod (3 ^ a))) hsub
    have hmod : ((3 ^ a : ℕ) : ZMod (3 ^ a)) = 0 := ZMod.natCast_self _
    simpa only [Nat.cast_add, Nat.cast_mul, hmod, zero_mul, zero_add] using hc.symm
  rw [show ((2 ^ m : ℕ) : ZMod (3 ^ a)) * ξ *
      (tstep^[m] r : ZMod (3 ^ a)) = ξ * (N : ZMod (3 ^ a)) by
        calc
          _ = ξ * (((2 ^ m : ℕ) : ZMod (3 ^ a)) *
              (tstep^[m] r : ZMod (3 ^ a))) := by ring
          _ = _ := by rw [hiter]]
  rw [stdAddChar_lift_three_pow a k N ξ]
  change ZMod.stdAddChar (((3 ^ k * ξ.val : ℕ) : ZMod (3 ^ (a + k))) *
      (N : ZMod (3 ^ (a + k)))) *
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((η.val * N : ℕ) : ℂ) / (3 ^ (a + k) : ℂ)))) = _
  rw [exp_neg_nat_eq_stdAddChar]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  unfold overPrecFrequencyZMod
  push_cast
  ring

/-- On one slice, the start character factors into the twist at the iterate and the negative
over-precision numerator phase. -/
theorem start_phase_eq_twistedParity_mul {m a k r : ℕ} (η : ZMod (3 ^ k))
    (hr : r < 2 ^ m) (ha : oddCount r m = a) :
    (paritySign (tstep^[m] r) : ℂ) *
        ZMod.stdAddChar (η * (r : ZMod (3 ^ k))) =
      twistedParity m a k η (tstep^[m] r : ZMod (3 ^ a)) *
        Complex.exp (-(2 * Real.pi * Complex.I *
          (((η.val * (2 ^ m * tstep^[m] r - 3 ^ a * r) : ℕ) : ℂ) /
            (3 ^ (a + k) : ℂ)))) := by
  rw [stdAddChar_mul_natCast_eq_exp]
  unfold twistedParity
  have hy : tstep^[m] r < 3 ^ a := by
    simpa [ha] using tstep_iterate_lt_three_pow hr
  rw [ZMod.val_natCast_of_lt hy]
  conv_rhs => rw [mul_assoc]
  apply congrArg (fun z : ℂ => (paritySign (tstep^[m] r) : ℂ) * z)
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have hle := three_pow_mul_le_two_pow_iterate ha
  have hsub : 3 ^ a * r + (2 ^ m * tstep^[m] r - 3 ^ a * r) =
      2 ^ m * tstep^[m] r := Nat.add_sub_of_le hle
  have hpow : (3 : ℂ) ^ (a + k) = 3 ^ a * 3 ^ k := by rw [pow_add]
  rw [hpow]
  field_simp
  have hback :
      2 ^ m * tstep^[m] r - (2 ^ m * tstep^[m] r - 3 ^ a * r) = 3 ^ a * r := by
    omega
  have hbackZ :
      ((2 ^ m * tstep^[m] r : ℕ) : ℤ) -
          ((2 ^ m * tstep^[m] r - 3 ^ a * r : ℕ) : ℤ) =
        ((3 ^ a * r : ℕ) : ℤ) := by
    rw [← Int.ofNat_sub (Nat.sub_le _ _)]
    exact_mod_cast hback
  have hinner :
      ((2 ^ m * tstep^[m] r : ℕ) : ℂ) -
          ((2 ^ m * tstep^[m] r - 3 ^ a * r : ℕ) : ℂ) =
        ((3 ^ a * r : ℕ) : ℂ) := by
    exact_mod_cast hbackZ
  rw [show (2 ^ m * tstep^[m] r : ℂ) +
      -(2 ^ m * tstep^[m] r - 3 ^ a * r : ℕ) = (3 ^ a * r : ℕ) by
        simpa [sub_eq_add_neg] using hinner]
  push_cast
  ring

/-- The numerator-side character sum produced by twisted Fourier inversion.  The remaining
reindexing by the unit `2^m` turns this into an over-precision slice character. -/
noncomputable def twistedNumeratorSum (m a k : ℕ) (η : ZMod (3 ^ k))
    (ξ : ZMod (3 ^ a)) : ℂ :=
  ∑ r ∈ levelSet m a,
    ZMod.stdAddChar (ξ * (tstep^[m] r : ZMod (3 ^ a))) *
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((η.val * (2 ^ m * tstep^[m] r - 3 ^ a * r) : ℕ) : ℂ) /
          (3 ^ (a + k) : ℂ))))

/-- The numerator character sum with its frequency represented directly in the fine cyclic
group. -/
noncomputable def overPrecZModSum (m a k : ℕ) (ζ : ZMod (3 ^ (a + k))) : ℂ :=
  ∑ r ∈ levelSet m a,
    ZMod.stdAddChar (ζ *
      ((2 ^ m * tstep^[m] r - 3 ^ a * r : ℕ) : ZMod (3 ^ (a + k))))

/-- The reindexed inner sum in ordinary exponential notation.  Its right-hand side is exactly
the defining sum of `overPrecChar` at the natural frequency `overPrecFrequencyNat`. -/
theorem overPrecZModSum_eq_exp_frequencyNat (m a k : ℕ) (η : ZMod (3 ^ k))
    (ξ : ZMod (3 ^ a)) :
    overPrecZModSum m a k (overPrecFrequencyZMod a k η ξ) =
      ∑ r ∈ levelSet m a,
        Complex.exp (2 * Real.pi * Complex.I *
          (((overPrecFrequencyNat a k η ξ *
              (2 ^ m * tstep^[m] r - 3 ^ a * r) : ℕ) : ℂ) /
            (3 ^ (a + k) : ℂ))) := by
  unfold overPrecZModSum
  apply Finset.sum_congr rfl
  intro r hr
  rw [← overPrecFrequencyNat_cast]
  rw [show (overPrecFrequencyNat a k η ξ : ZMod (3 ^ (a + k))) *
      ((2 ^ m * tstep^[m] r - 3 ^ a * r : ℕ) : ZMod (3 ^ (a + k))) =
        ((overPrecFrequencyNat a k η ξ *
          (2 ^ m * tstep^[m] r - 3 ^ a * r) : ℕ) : ZMod (3 ^ (a + k))) by norm_cast]
  rw [stdAddChar_nat_eq_exp]

/-- After multiplying the Fourier frequency by `2^m`, the inner twisted sum is exactly a
fine-modulus numerator character sum. -/
theorem twistedNumeratorSum_two_pow (m a k : ℕ) (η : ZMod (3 ^ k))
    (ξ : ZMod (3 ^ a)) :
    twistedNumeratorSum m a k η (((2 ^ m : ℕ) : ZMod (3 ^ a)) * ξ) =
      overPrecZModSum m a k (overPrecFrequencyZMod a k η ξ) := by
  unfold twistedNumeratorSum overPrecZModSum
  apply Finset.sum_congr rfl
  intro r hr
  exact twistedNumerator_term_eq η ξ (Finset.mem_filter.mp hr).2

/-- Multiplication by `2^m` permutes `ZMod (3^a)`. -/
noncomputable def twoPowMulEquiv (m a : ℕ) : ZMod (3 ^ a) ≃ ZMod (3 ^ a) :=
  Units.mulLeft (ZMod.unitOfCoprime (2 ^ m)
    (Nat.Coprime.pow m a (by decide : Nat.Coprime 2 3)))

@[simp] theorem twoPowMulEquiv_apply (m a : ℕ) (ξ : ZMod (3 ^ a)) :
    twoPowMulEquiv m a ξ = ((2 ^ m : ℕ) : ZMod (3 ^ a)) * ξ := by
  simp [twoPowMulEquiv, Units.mulLeft, ZMod.coe_unitOfCoprime]

/-- Exact per-slice twisted Fourier expansion.  This is the finite Fourier seam in Edge 1 of
`C1PLUS-NEXT.md`; no estimate has yet been applied. -/
theorem sliceStartTwist_eq_fourier_twisted (m a k : ℕ) (η : ZMod (3 ^ k)) :
    sliceStartTwist m a k η =
      ∑ ξ : ZMod (3 ^ a), twistedHat m a k η ξ * twistedNumeratorSum m a k η ξ := by
  rw [show sliceStartTwist m a k η =
      ∑ r ∈ levelSet m a,
        twistedParity m a k η (tstep^[m] r : ZMod (3 ^ a)) *
          Complex.exp (-(2 * Real.pi * Complex.I *
            (((η.val * (2 ^ m * tstep^[m] r - 3 ^ a * r) : ℕ) : ℂ) /
              (3 ^ (a + k) : ℂ)))) by
    unfold sliceStartTwist
    apply Finset.sum_congr rfl
    intro r hr
    exact start_phase_eq_twistedParity_mul η
      (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
      (Finset.mem_filter.mp hr).2]
  unfold twistedNumeratorSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  let E : ℂ := Complex.exp (-(2 * Real.pi * Complex.I *
    (((η.val * (2 ^ m * tstep^[m] r - 3 ^ a * r) : ℕ) : ℂ) /
      (3 ^ (a + k) : ℂ))))
  change twistedParity m a k η (tstep^[m] r : ZMod (3 ^ a)) * E =
    ∑ x : ZMod (3 ^ a), twistedHat m a k η x *
      (ZMod.stdAddChar (x * (tstep^[m] r : ZMod (3 ^ a))) * E)
  calc
    _ = (∑ x : ZMod (3 ^ a), twistedHat m a k η x *
          ZMod.stdAddChar (x * (tstep^[m] r : ZMod (3 ^ a)))) * E := by
      rw [← twistedParity_eq_fourier]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring

/-- Exact per-slice expansion after the `2^m` frequency permutation.  Every inner term is now
a fine-modulus numerator character, ready for the 3-adic frequency normalization. -/
theorem sliceStartTwist_eq_fourier_overPrecZMod (m a k : ℕ) (η : ZMod (3 ^ k)) :
    sliceStartTwist m a k η =
      ∑ ξ : ZMod (3 ^ a),
        twistedHat m a k η (((2 ^ m : ℕ) : ZMod (3 ^ a)) * ξ) *
          overPrecZModSum m a k (overPrecFrequencyZMod a k η ξ) := by
  rw [sliceStartTwist_eq_fourier_twisted]
  rw [← (twoPowMulEquiv m a).sum_comp]
  simp only [twoPowMulEquiv_apply]
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [twistedNumeratorSum_two_pow]

end CollatzMoonshot.Conjugacy
