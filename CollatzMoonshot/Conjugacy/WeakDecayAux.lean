/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.C1

/-!
# Exact Fourier algebra for C1⁺

This file contains the finite, exact part of the reduction from over-precision slice-character
decay to decay of every start residue class.  The analytic estimates remain in `WeakDecay.lean`;
the identities here isolate their input without changing any frozen statement.
-/

namespace CollatzMoonshot.Conjugacy

open CollatzMoonshot.FrontB

/-- The Fourier transform of the signed start measure on `ZMod (3^k)`. -/
noncomputable def startTwist (m k : ℕ) (η : ZMod (3 ^ k)) : ℂ :=
  ∑ r ∈ Finset.range (2 ^ m),
    (paritySign (tstep^[m] r) : ℂ) *
      ZMod.stdAddChar (η * (r : ZMod (3 ^ k)))

/-- The contribution of one odd-count slice to `startTwist`. -/
noncomputable def sliceStartTwist (m a k : ℕ) (η : ZMod (3 ^ k)) : ℂ :=
  ∑ r ∈ levelSet m a,
    (paritySign (tstep^[m] r) : ℂ) *
      ZMod.stdAddChar (η * (r : ZMod (3 ^ k)))

/-- On a fixed slice, the natural subtraction used by `overPrecChar` is exact. -/
theorem three_pow_mul_le_two_pow_iterate {m a r : ℕ} (ha : oddCount r m = a) :
    3 ^ a * r ≤ 2 ^ m * tstep^[m] r := by
  have h := tstep_iterate_identity m r
  change ones (traceWord r m) = a at ha
  rw [ha] at h
  omega

/-- The numerator in `overPrecChar` is exactly the parity-word numerator from the iterate
identity.  This removes all ambiguity from the natural subtraction before the character
manipulations begin. -/
theorem iterateNumerator_eq_numer {m a r : ℕ} (ha : oddCount r m = a) :
    2 ^ m * tstep^[m] r - 3 ^ a * r = numer (traceWord r m) := by
  have h := tstep_iterate_identity m r
  change ones (traceWord r m) = a at ha
  rw [ha] at h
  omega

/-- Orthogonality of additive characters, normalized as a residue-class indicator. -/
theorem zmod_class_indicator (M : ℕ) [NeZero M] (y c : ZMod M) :
    ∑ η : ZMod M, (M : ℂ)⁻¹ * ZMod.stdAddChar (η * (y - c)) =
      if y = c then 1 else 0 := by
  rw [← Finset.mul_sum]
  rw [AddChar.sum_mulShift (y - c) (ZMod.isPrimitive_stdAddChar M)]
  by_cases h : y = c
  · simp [h]
  · have hne : y - c ≠ 0 := sub_ne_zero.mpr h
    simp [hne, h]

/-- The signed mass of a bounded start residue class is exactly the inverse Fourier transform of
`startTwist`.  The condition `c < 3^k` is the canonical-representative condition; classes outside
that range are empty and are handled separately by `biasClassPow_eq_zero_of_pow_le` below. -/
theorem biasClassPow_cast_eq_fourier (m k c : ℕ) (hc : c < 3 ^ k) :
    (biasClassPow m k c : ℂ) =
      ∑ η : ZMod (3 ^ k),
        ((3 ^ k : ℕ) : ℂ)⁻¹ * ZMod.stdAddChar (-(η * (c : ZMod (3 ^ k)))) *
          startTwist m k η := by
  let M := 3 ^ k
  have hM : NeZero M := ⟨pow_ne_zero k (by norm_num)⟩
  let _ : NeZero M := hM
  have hcM : c < M := by simpa [M] using hc
  have hind (r : ℕ) :
      ∑ η : ZMod M, (M : ℂ)⁻¹ *
          ZMod.stdAddChar (-(η * (c : ZMod M))) *
          ZMod.stdAddChar (η * (r : ZMod M)) =
        if r % M = c then 1 else 0 := by
    have hchar (η : ZMod M) :
        ZMod.stdAddChar (-(η * (c : ZMod M))) *
            ZMod.stdAddChar (η * (r : ZMod M)) =
          ZMod.stdAddChar (η * ((r : ZMod M) - (c : ZMod M))) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp_rw [show ∀ η : ZMod M,
        (M : ℂ)⁻¹ * ZMod.stdAddChar (-(η * (c : ZMod M))) *
            ZMod.stdAddChar (η * (r : ZMod M)) =
          (M : ℂ)⁻¹ *
            (ZMod.stdAddChar (-(η * (c : ZMod M))) *
              ZMod.stdAddChar (η * (r : ZMod M))) by intro η; ring]
    simp_rw [hchar]
    rw [zmod_class_indicator M (r : ZMod M) (c : ZMod M)]
    have heq : (r : ZMod M) = (c : ZMod M) ↔ r % M = c := by
      constructor
      · intro h
        have hval := congrArg ZMod.val h
        simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hcM] using hval
      · intro h
        apply ZMod.val_injective
        simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hcM]
    simp only [heq]
  change (biasClassPow m k c : ℂ) = _
  rw [show (biasClassPow m k c : ℂ) =
      ∑ r ∈ Finset.range (2 ^ m),
        (paritySign (tstep^[m] r) : ℂ) * (if r % M = c then 1 else 0) by
    unfold biasClassPow
    push_cast
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    rw [paritySign_eq_ite]
    split_ifs <;> norm_num]
  unfold startTwist
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  change (paritySign (tstep^[m] r) : ℂ) * (if r % M = c then 1 else 0) =
    ∑ x : ZMod M, (M : ℂ)⁻¹ * ZMod.stdAddChar (-(x * (c : ZMod M))) *
      ((paritySign (tstep^[m] r) : ℂ) * ZMod.stdAddChar (x * (r : ZMod M)))
  rw [show (∑ x : ZMod M, (M : ℂ)⁻¹ * ZMod.stdAddChar (-(x * (c : ZMod M))) *
      ((paritySign (tstep^[m] r) : ℂ) * ZMod.stdAddChar (x * (r : ZMod M)))) =
      (paritySign (tstep^[m] r) : ℂ) *
        ∑ x : ZMod M, (M : ℂ)⁻¹ * ZMod.stdAddChar (-(x * (c : ZMod M))) *
          ZMod.stdAddChar (x * (r : ZMod M)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring]
  rw [hind]

/-- A noncanonical class label selects no starts. -/
theorem biasClassPow_eq_zero_of_pow_le (m k c : ℕ) (hc : 3 ^ k ≤ c) :
    biasClassPow m k c = 0 := by
  unfold biasClassPow
  apply Finset.sum_eq_zero
  intro r hr
  have hmod : r % 3 ^ k < 3 ^ k := Nat.mod_lt _ (pow_pos (by norm_num) _)
  have hne : r % 3 ^ k ≠ c := by omega
  exact False.elim (hne (Finset.mem_filter.mp hr).2)

/-- The full start transform is the sum of its `m+1` odd-count slices. -/
theorem startTwist_eq_sum_sliceStartTwist (m k : ℕ) (η : ZMod (3 ^ k)) :
    startTwist m k η =
      ∑ a ∈ Finset.range (m + 1), sliceStartTwist m a k η := by
  unfold startTwist sliceStartTwist levelSet
  exact (Finset.sum_fiberwise_of_maps_to
    (s := Finset.range (2 ^ m)) (t := Finset.range (m + 1))
    (g := fun r => oddCount r m)
    (fun r _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (oddCount_le r m)))
    (fun r => (paritySign (tstep^[m] r) : ℂ) *
      ZMod.stdAddChar (η * (r : ZMod (3 ^ k))))).symm

/-- The zero Fourier mode is C1's bias. -/
theorem startTwist_zero (m k : ℕ) :
    startTwist m k 0 = (bias m : ℂ) := by
  unfold startTwist bias
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  rw [paritySign_eq_ite]
  split_ifs <;> norm_num

/-- On each slice the zero Fourier mode is the signed slice count. -/
theorem sliceStartTwist_zero (m a k : ℕ) :
    sliceStartTwist m a k 0 = (levelSign m a : ℂ) := by
  unfold sliceStartTwist levelSign
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  rw [paritySign_eq_ite]
  split_ifs <;> norm_num

/-- The elementary bound used for all discarded slices. -/
theorem norm_sliceStartTwist_le_card (m a k : ℕ) (η : ZMod (3 ^ k)) :
    ‖sliceStartTwist m a k η‖ ≤ (levelSet m a).card := by
  unfold sliceStartTwist
  calc
    ‖∑ r ∈ levelSet m a,
        (paritySign (tstep^[m] r) : ℂ) *
          ZMod.stdAddChar (η * (r : ZMod (3 ^ k)))‖ ≤
        ∑ r ∈ levelSet m a,
          ‖(paritySign (tstep^[m] r) : ℂ) *
            ZMod.stdAddChar (η * (r : ZMod (3 ^ k)))‖ := norm_sum_le _ _
    _ = (levelSet m a).card := by
      simp [abs_paritySign, AddChar.norm_apply]

/-- The exact residue-class expansion already split into odd-count slices.  This is the algebraic
starting point for the main-window/tail estimate in `weakDecayOnZ3_of_overPrecSliceCharDecay`. -/
theorem biasClassPow_cast_eq_fourier_slices (m k c : ℕ) (hc : c < 3 ^ k) :
    (biasClassPow m k c : ℂ) =
      ∑ η : ZMod (3 ^ k),
        ((3 ^ k : ℕ) : ℂ)⁻¹ * ZMod.stdAddChar (-(η * (c : ZMod (3 ^ k)))) *
          ∑ a ∈ Finset.range (m + 1), sliceStartTwist m a k η := by
  rw [biasClassPow_cast_eq_fourier m k c hc]
  apply Finset.sum_congr rfl
  intro η hη
  rw [startTwist_eq_sum_sliceStartTwist]

end CollatzMoonshot.Conjugacy
