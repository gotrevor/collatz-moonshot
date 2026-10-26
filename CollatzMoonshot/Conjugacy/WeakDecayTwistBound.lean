/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.WeakDecayTwist

/-!
# Fourier-weight bound for the C1⁺ twist

The shifted Fourier coefficients used in `WeakDecayTwist.lean` are compared with the ordinary
least-residue parity coefficients at the finer modulus.  The comparison loses `3^k`; this loss
is necessary for a shift which can approach the pole to within `1 / 3^k` of a coarse grid step,
and is harmless because the extra precision `k` is fixed in `WeakDecayOnZ3`.
-/

namespace CollatzMoonshot.Conjugacy

open CollatzMoonshot.FrontB

/-- The fine-modulus character occurring in a coefficient of `twistedParity`. -/
def twistedHatFrequency (m a k : ℕ) (η : ZMod (3 ^ k)) (ξ : ZMod (3 ^ a)) :
    ZMod (3 ^ (a + k)) :=
  ((η.val * 2 ^ m : ℕ) : ZMod (3 ^ (a + k))) -
    ((3 ^ k * ξ.val : ℕ) : ZMod (3 ^ (a + k)))

/-- A summand in `twistedHat` is a power of one fine-modulus character, with the parity sign
absorbed into the minus sign. -/
theorem twistedParity_addChar_term (m a k : ℕ) (η : ZMod (3 ^ k))
    (ξ : ZMod (3 ^ a)) (n : ℕ) (hn : n < 3 ^ a) :
    twistedParity m a k η (n : ZMod (3 ^ a)) *
        ZMod.stdAddChar (- (ξ * (n : ZMod (3 ^ a)))) =
      (-ZMod.stdAddChar (twistedHatFrequency m a k η ξ)) ^ n := by
  have htwist :
      Complex.exp (2 * Real.pi * Complex.I *
          (((η.val * 2 ^ m * n : ℕ) : ℂ) / (3 ^ (a + k) : ℂ))) =
        ZMod.stdAddChar
          ((η.val * 2 ^ m * n : ℕ) : ZMod (3 ^ (a + k))) := by
    exact (stdAddChar_nat_eq_exp (a + k) (η.val * 2 ^ m * n)).symm
  have hlift :
      ZMod.stdAddChar (- (ξ * (n : ZMod (3 ^ a)))) =
        ZMod.stdAddChar
          (-(((3 ^ k * ξ.val : ℕ) : ZMod (3 ^ (a + k))) *
            (n : ZMod (3 ^ (a + k))))) := by
    rw [AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv]
    rw [stdAddChar_lift_three_pow]
  have hchars :
      ZMod.stdAddChar
          ((η.val * 2 ^ m * n : ℕ) : ZMod (3 ^ (a + k))) *
        ZMod.stdAddChar
          (-(((3 ^ k * ξ.val : ℕ) : ZMod (3 ^ (a + k))) *
            (n : ZMod (3 ^ (a + k))))) =
      ZMod.stdAddChar (n • twistedHatFrequency m a k η ξ) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    unfold twistedHatFrequency
    simp only [nsmul_eq_mul]
    push_cast
    ring
  unfold twistedParity
  rw [ZMod.val_natCast_of_lt hn, htwist, hlift]
  rw [show (paritySign n : ℂ) = (-1 : ℂ) ^ n by simp [paritySign]]
  rw [mul_assoc, hchars, AddChar.map_nsmul_eq_pow, ← mul_pow]
  congr 1
  ring

/-- Geometric-series form of a shifted Fourier coefficient. -/
theorem twistedHat_eq_geom (m a k : ℕ) (η : ZMod (3 ^ k))
    (ξ : ZMod (3 ^ a)) :
    twistedHat m a k η ξ = ((3 ^ a : ℕ) : ℂ)⁻¹ *
      ∑ n ∈ Finset.range (3 ^ a),
        (-ZMod.stdAddChar (twistedHatFrequency m a k η ξ)) ^ n := by
  unfold twistedHat
  congr 1
  rw [sum_zmod_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  exact twistedParity_addChar_term m a k η ξ n (Finset.mem_range.mp hn)

/-- Pointwise comparison with an ordinary parity coefficient at the fine modulus.  The factor
`3^k` is the ratio between the fine and coarse moduli. -/
theorem norm_twistedHat_le_fine (m a k : ℕ) (η : ZMod (3 ^ k))
    (ξ : ZMod (3 ^ a)) :
    ‖twistedHat m a k η ξ‖ ≤
      (3 : ℝ) ^ k *
        ‖gHatZ (a + k) (-twistedHatFrequency m a k η ξ)‖ := by
  let ω := ZMod.stdAddChar (twistedHatFrequency m a k η ξ)
  have hωnorm : ‖ω‖ = 1 := AddChar.norm_apply _ _
  have hω : ω ≠ -1 := by
    dsimp [ω]
    simpa using stdAddChar_ne_neg_one (a + k)
      (-twistedHatFrequency m a k η ξ)
  have hq : -ω ≠ 1 := by
    intro h
    apply hω
    linear_combination -h
  have hnum : ‖(-ω) ^ (3 ^ a) - 1‖ ≤ 2 := by
    calc
      ‖(-ω) ^ (3 ^ a) - 1‖ ≤ ‖(-ω) ^ (3 ^ a)‖ + ‖1‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_neg, hωnorm]; norm_num
  have hden : ‖-ω - 1‖ = ‖1 + ω‖ := by
    rw [show -ω - 1 = -(1 + ω) by ring, norm_neg]
  rw [twistedHat_eq_geom, geom_sum_eq hq]
  rw [norm_mul, norm_inv, norm_div, hden]
  rw [norm_gHatZ_closed]
  simp only [neg_neg, Nat.cast_pow, Nat.cast_ofNat]
  norm_num only [norm_pow]
  rw [show ‖(3 : ℂ)‖ = 3 by norm_num]
  change ((3 ^ a : ℝ))⁻¹ *
      (‖(-ω) ^ (3 ^ a) - 1‖ / ‖1 + ω‖) ≤
    3 ^ k * (2 / (3 ^ (a + k) * ‖1 + ω‖))
  have hM : (0 : ℝ) < 3 ^ a := by positivity
  have hP : (0 : ℝ) < 3 ^ (a + k) := by positivity
  have hadd : 1 + ω ≠ 0 := by
    intro h
    apply hω
    linear_combination h
  have hdenpos : 0 < ‖1 + ω‖ := norm_pos_iff.mpr hadd
  rw [show (3 : ℝ) ^ (a + k) = 3 ^ a * 3 ^ k by rw [pow_add]]
  rw [inv_eq_one_div]
  calc
    1 / 3 ^ a * (‖(-ω) ^ (3 ^ a) - 1‖ / ‖1 + ω‖) =
        ‖(-ω) ^ (3 ^ a) - 1‖ / (3 ^ a * ‖1 + ω‖) := by
          field_simp
    _ ≤ 2 / (3 ^ a * ‖1 + ω‖) := by
      exact (div_le_div_iff_of_pos_right (mul_pos hM hdenpos)).2 hnum
    _ = 3 ^ k * (2 / (3 ^ a * 3 ^ k * ‖1 + ω‖)) := by
      have hk : (0 : ℝ) < 3 ^ k := by positivity
      field_simp

/-- The coarse frequency grid embeds in the fine one after the shift. -/
theorem neg_twistedHatFrequency_injective (m a k : ℕ) (η : ZMod (3 ^ k)) :
    Function.Injective (fun ξ : ZMod (3 ^ a) => -twistedHatFrequency m a k η ξ) := by
  intro ξ ξ' h
  have hfreq : twistedHatFrequency m a k η ξ =
      twistedHatFrequency m a k η ξ' := by
    have := congrArg Neg.neg h
    simpa using this
  have hcast :
      ((3 ^ k * ξ.val : ℕ) : ZMod (3 ^ (a + k))) =
        ((3 ^ k * ξ'.val : ℕ) : ZMod (3 ^ (a + k))) := by
    unfold twistedHatFrequency at hfreq
    exact sub_right_inj.mp hfreq
  have hpow : 3 ^ (a + k) = 3 ^ k * 3 ^ a := by
    rw [Nat.add_comm, pow_add]
  have hξlt : 3 ^ k * ξ.val < 3 ^ (a + k) := by
    rw [hpow]
    exact Nat.mul_lt_mul_of_pos_left ξ.val_lt (by positivity)
  have hξ'lt : 3 ^ k * ξ'.val < 3 ^ (a + k) := by
    rw [hpow]
    exact Nat.mul_lt_mul_of_pos_left ξ'.val_lt (by positivity)
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hξlt, ZMod.val_natCast_of_lt hξ'lt] at hval
  apply ZMod.val_injective
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 3 ^ k) hval

/-- Restricting the fine parity coefficients to the shifted coarse grid cannot increase their
total mass. -/
theorem sum_norm_gHatZ_neg_twistedHatFrequency_le (m a k : ℕ)
    (η : ZMod (3 ^ k)) :
    (∑ ξ : ZMod (3 ^ a),
        ‖gHatZ (a + k) (-twistedHatFrequency m a k η ξ)‖) ≤
      4 * (a + k + 1) := by
  let f := fun ξ : ZMod (3 ^ a) => -twistedHatFrequency m a k η ξ
  have hinj : Set.InjOn f (Finset.univ : Finset (ZMod (3 ^ a))) :=
    (neg_twistedHatFrequency_injective m a k η).injOn
  calc
    (∑ ξ : ZMod (3 ^ a), ‖gHatZ (a + k) (f ξ)‖) =
        ∑ ζ ∈ (Finset.univ : Finset (ZMod (3 ^ a))).image f,
          ‖gHatZ (a + k) ζ‖ :=
      (Finset.sum_image (f := fun ζ => ‖gHatZ (a + k) ζ‖) hinj).symm
    _ ≤ ∑ ζ : ZMod (3 ^ (a + k)), ‖gHatZ (a + k) ζ‖ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => norm_nonneg _)
    _ ≤ 4 * (a + k + 1) := by
      convert sum_norm_gHatZ_le (a + k) using 1 <;> (push_cast; ring)

/-- The complete family of shifted coefficients has fixed-precision logarithmic mass. -/
theorem sum_norm_twistedHat_le (m a k : ℕ) (η : ZMod (3 ^ k)) :
    (∑ ξ : ZMod (3 ^ a), ‖twistedHat m a k η ξ‖) ≤
      (3 : ℝ) ^ k * (4 * (a + k + 1)) := by
  calc
    (∑ ξ : ZMod (3 ^ a), ‖twistedHat m a k η ξ‖) ≤
        ∑ ξ : ZMod (3 ^ a),
          (3 : ℝ) ^ k *
            ‖gHatZ (a + k) (-twistedHatFrequency m a k η ξ)‖ := by
      exact Finset.sum_le_sum (fun ξ _ => norm_twistedHat_le_fine m a k η ξ)
    _ = (3 : ℝ) ^ k *
        ∑ ξ : ZMod (3 ^ a),
          ‖gHatZ (a + k) (-twistedHatFrequency m a k η ξ)‖ := by
      rw [Finset.mul_sum]
    _ ≤ (3 : ℝ) ^ k * (4 * (a + k + 1)) := by
      gcongr
      exact sum_norm_gHatZ_neg_twistedHatFrequency_le m a k η

/-- After removing the exact `3`-power from a nonzero start frequency, the fine-modulus
character sum is literally the same exponential sum at the reduced precision. -/
theorem overPrecZModSum_eq_normalized_exp {m a k : ℕ} {η : ZMod (3 ^ k)}
    (hη : η ≠ 0) (ξ : ZMod (3 ^ a)) :
    let v := padicValNat 3 η.val
    overPrecZModSum m a k (overPrecFrequencyZMod a k η ξ) =
      ∑ r ∈ levelSet m a,
        Complex.exp ((2 * Real.pi * Complex.I *
          ((overPrecFrequencyUnit a k η ξ *
              (2 ^ m * tstep^[m] r - 3 ^ a * r) : ℕ) : ℂ)) /
            (3 ^ (a + (k - v)) : ℂ)) := by
  let v := padicValNat 3 η.val
  have hnorm := overPrecFrequencyNat_normalize ξ hη
  have hvk : v < k := hnorm.1
  have hfac : overPrecFrequencyNat a k η ξ =
      3 ^ v * overPrecFrequencyUnit a k η ξ := hnorm.2.1
  rw [overPrecZModSum_eq_exp_frequencyNat]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  rw [hfac]
  push_cast
  have hexp : a + k = v + (a + (k - v)) := by omega
  rw [show (3 : ℂ) ^ (a + k) = 3 ^ v * 3 ^ (a + (k - v)) by
    rw [hexp, pow_add]]
  dsimp only [v]
  field_simp

/-- A uniform estimate for the normalized fine character sums bounds one twisted slice by the
Fourier-weight mass. -/
theorem norm_sliceStartTwist_le_of_normalized {m a k : ℕ} {η : ZMod (3 ^ k)}
    (hη : η ≠ 0) {B : ℝ} (hB : 0 ≤ B)
    (hinner : ∀ ξ : ZMod (3 ^ a),
      ‖∑ r ∈ levelSet m a,
        Complex.exp ((2 * Real.pi * Complex.I *
          ((overPrecFrequencyUnit a k η ξ *
              (2 ^ m * tstep^[m] r - 3 ^ a * r) : ℕ) : ℂ)) /
            (3 ^ (a + (k - padicValNat 3 η.val)) : ℂ))‖ ≤ B) :
    ‖sliceStartTwist m a k η‖ ≤
      ((3 : ℝ) ^ k * (4 * (a + k + 1))) * B := by
  rw [sliceStartTwist_eq_fourier_overPrecZMod]
  calc
    ‖∑ ξ : ZMod (3 ^ a),
        twistedHat m a k η (((2 ^ m : ℕ) : ZMod (3 ^ a)) * ξ) *
          overPrecZModSum m a k (overPrecFrequencyZMod a k η ξ)‖ ≤
        ∑ ξ : ZMod (3 ^ a),
          ‖twistedHat m a k η (((2 ^ m : ℕ) : ZMod (3 ^ a)) * ξ)‖ * B := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
      rw [norm_mul]
      gcongr
      rw [overPrecZModSum_eq_normalized_exp hη]
      exact hinner ξ
    _ = (∑ ξ : ZMod (3 ^ a), ‖twistedHat m a k η ξ‖) * B := by
      rw [← Finset.sum_mul]
      congr 1
      exact (twoPowMulEquiv m a).sum_comp
        (fun ξ => ‖twistedHat m a k η ξ‖)
    _ ≤ ((3 : ℝ) ^ k * (4 * (a + k + 1))) * B := by
      gcongr
      exact sum_norm_twistedHat_le m a k η

/-- Sum a uniform central-slice estimate and control the complementary slices by cardinality. -/
theorem norm_startTwist_le_of_slice (m k : ℕ) (η : ZMod (3 ^ k)) {E : ℝ}
    (hE : 0 ≤ E)
    (hslice : ∀ a, m ≤ 4 * a → a ≤ 11 * m / 20 →
      ‖sliceStartTwist m a k η‖ ≤ E * (levelSet m a).card) :
    ‖startTwist m k η‖ ≤ E * 2 ^ m + (outOddSet m).card := by
  let I := Finset.range (m + 1)
  let L := I.filter (fun a => m ≤ 4 * a ∧ a ≤ 11 * m / 20)
  let H := I.filter (fun a => 4 * a < m ∨ 11 * m / 20 < a)
  have hLcard : ∑ a ∈ L, ((levelSet m a).card : ℝ) ≤ 2 ^ m := by
    calc
      ∑ a ∈ L, ((levelSet m a).card : ℝ) ≤
          ∑ a ∈ I, ((levelSet m a).card : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = 2 ^ m := by
        exact_mod_cast sum_levelSet_card m
  have hlow : ‖∑ a ∈ L, sliceStartTwist m a k η‖ ≤ E * 2 ^ m := by
    calc
      ‖∑ a ∈ L, sliceStartTwist m a k η‖ ≤
          ∑ a ∈ L, ‖sliceStartTwist m a k η‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ L, E * (levelSet m a).card := by
        exact Finset.sum_le_sum fun a ha => hslice a
          (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
      _ = E * ∑ a ∈ L, ((levelSet m a).card : ℝ) := by rw [Finset.mul_sum]
      _ ≤ E * 2 ^ m := mul_le_mul_of_nonneg_left hLcard hE
  have hHcard : ∑ a ∈ H, ((levelSet m a).card : ℝ) = (outOddSet m).card := by
    exact_mod_cast sum_out_levelSet_card m
  have hhigh : ‖∑ a ∈ H, sliceStartTwist m a k η‖ ≤ (outOddSet m).card := by
    calc
      ‖∑ a ∈ H, sliceStartTwist m a k η‖ ≤
          ∑ a ∈ H, ‖sliceStartTwist m a k η‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ H, ((levelSet m a).card : ℝ) := by
        exact Finset.sum_le_sum fun a _ => norm_sliceStartTwist_le_card m a k η
      _ = (outOddSet m).card := hHcard
  have hpartition :
      ∑ a ∈ I, sliceStartTwist m a k η =
        (∑ a ∈ L, sliceStartTwist m a k η) +
          ∑ a ∈ H, sliceStartTwist m a k η := by
    have hs := Finset.sum_filter_add_sum_filter_not I
      (fun a => m ≤ 4 * a ∧ a ≤ 11 * m / 20)
      (fun a => sliceStartTwist m a k η)
    rw [show I.filter (fun a => ¬(m ≤ 4 * a ∧ a ≤ 11 * m / 20)) = H by
      ext a
      simp [H]
      omega] at hs
    exact hs.symm
  rw [startTwist_eq_sum_sliceStartTwist, hpartition]
  exact (norm_add_le _ _).trans (add_le_add hlow hhigh)

end CollatzMoonshot.Conjugacy
