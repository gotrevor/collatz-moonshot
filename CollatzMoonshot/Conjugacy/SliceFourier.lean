/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.SliceDecay

/-!
# C1 directly from slice character decay (2026-10-25)

A shortcut past `TruncatedSyracMixing` and Tao's §6.  For `r ∈ levelSet j a`, `y = T^j r < 3^a` is a
least residue mod `M = 3^a`, so the slice's signed count is `Σ_y mass(y)·g(y)`, with `g(y) = (−1)^y`
on `[0, M)`.  Expand `g` in additive characters of `ℤ/M`:
`ĝ(ξ) = (1/M)·2/(1 + e(−ξ/M))`, so `|ĝ(ξ)| = 1/(M·|cos(πξ/M)|)`, because `M` is odd.

* **Weights.**  `Σ_ξ |ĝ(ξ)| = O(log M) = O(a)`.  The frequencies with `v₃(ξ) = k` carry weight
  `O(3^{−k}·(a − k + 1))`.
* **Frequencies `ξ = 3^k u`, `3 ∤ u`.**  Here `F(ξ) = Σ_r e(u·T^j r / 3^{a−k})` is the character sum of
  the slice reduced mod `3^{a−k}`.  Given the `(a−k+1)`-th odd time `t`, that is the slice `(t−1, a−k)`.
  So `F(ξ)` is a mixture of `sliceChar (t−1) (a−k) u`.  The sub-slice ratios concentrate at `a/j`, and
  the exceptional `t` have binomially small mass.
* **Bound.**  `|levelSign j a|/#slice ≤ 3^{−a} + O(a)·sup_{k ≤ K} C·j^{−A} + O(a·3^{−K})`.  Take
  `K = ⌈2 log₃ j⌉` and `A = 2`.  The slices with `a/j` outside `[1/4, 11/20]` are the binomial tails
  already bounded in `Bridge3.lean` (`outOddSet`).
* **Checked** (`experiments/conjugacy/fourier_bias_check.py`):
  - the identity `levelSign = Σ_ξ conj(ĝ(ξ))·F(ξ)` is exact against brute-force Collatz at
    `(j,a) = (8,3), (10,5), (12,6), (12,7)`;
  - `Σ|ĝ| ≈ (2/π) ln M + 1`;
  - the level-`k` weights fall by about `3×` per level.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-! ## Pascal recursion and sub-slices -/

/-- The positive additive character occurring in `sliceChar`, separated out so its change of
modulus and periodicity can be used without unfolding the whole slice sum. -/
noncomputable def slicePhase (a ξ y : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((ξ * y : ℕ) : ℂ) / (3 ^ a : ℂ))

theorem slicePhase_scale (a ξ y : ℕ) :
    slicePhase (a + 1) (3 * ξ) y = slicePhase a ξ y := by
  unfold slicePhase
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

theorem slicePhase_add_mul_pow (a ξ y c : ℕ) :
    slicePhase a ξ (y + c * 3 ^ a) = slicePhase a ξ y := by
  unfold slicePhase
  rw [show
      2 * Real.pi * Complex.I * (((ξ * (y + c * 3 ^ a) : ℕ) : ℂ)) / (3 ^ a : ℂ) =
        2 * Real.pi * Complex.I * (((ξ * y : ℕ) : ℂ)) / (3 ^ a : ℂ) +
          (ξ * c : ℕ) * (2 * Real.pi * Complex.I) by
    push_cast
    field_simp]
  rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem oddCount_two_mul_succ (s j : ℕ) :
    oddCount (2 * s) (j + 1) = oddCount s j := by
  rw [oddCount_succ, tstep_two_mul]
  norm_num

theorem oddCount_two_mul_add_one_succ (s j : ℕ) :
    oddCount (2 * s + 1) (j + 1) = oddCount (3 * s + 2) j + 1 := by
  rw [oddCount_succ, tstep_two_mul_add_one]
  norm_num

/-- Split the next slice by the parity of its starting residue. -/
theorem sliceChar_succ_split (j a ξ : ℕ) :
    sliceChar (j + 1) (a + 1) (3 * ξ) =
      (∑ s ∈ Finset.range (2 ^ j),
        if oddCount s j = a + 1 then slicePhase (a + 1) (3 * ξ) (tstep^[j] s) else 0) +
      ∑ s ∈ Finset.range (2 ^ j),
        if oddCount (3 * s + 2) j = a then
          slicePhase (a + 1) (3 * ξ) (tstep^[j] (3 * s + 2)) else 0 := by
  unfold sliceChar levelSet slicePhase
  rw [Finset.sum_filter, pow_succ, mul_comm, sum_range_two_mul, Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro s hs
    rw [oddCount_two_mul_succ, Function.iterate_succ_apply, tstep_two_mul]
  · apply Finset.sum_congr rfl
    intro s hs
    rw [oddCount_two_mul_add_one_succ, Function.iterate_succ_apply, tstep_two_mul_add_one]
    simp only [Nat.add_right_cancel_iff]

theorem sliceChar_eq_sum_phase (j a ξ : ℕ) :
    sliceChar j a ξ = ∑ s ∈ Finset.range (2 ^ j),
      if oddCount s j = a then slicePhase a ξ (tstep^[j] s) else 0 := by
  unfold sliceChar levelSet slicePhase
  rw [Finset.sum_filter]

/-- Multiplication by three followed by addition of two permutes the residues modulo `2^j`. -/
noncomputable def affineThreeEquiv (j : ℕ) : ZMod (2 ^ j) ≃ ZMod (2 ^ j) :=
  (Units.mulLeft (ZMod.unitOfCoprime 3
    (Nat.Coprime.pow_right j (by decide : Nat.Coprime 3 2)))).trans
      (Equiv.addRight (2 : ZMod (2 ^ j)))

theorem affineThreeEquiv_apply (j : ℕ) (x : ZMod (2 ^ j)) :
    affineThreeEquiv j x = 3 * x + 2 := by
  simp [affineThreeEquiv, Units.mulLeft, ZMod.coe_unitOfCoprime]

theorem affineThreeEquiv_val (j : ℕ) (x : ZMod (2 ^ j)) :
    (affineThreeEquiv j x).val = (3 * x.val + 2) % 2 ^ j := by
  rw [affineThreeEquiv_apply, ZMod.val_add, ZMod.val_mul]
  rw [ZMod.val_ofNat, ZMod.val_ofNat]
  have hmul : (3 % 2 ^ j * x.val) % 2 ^ j = (3 * x.val) % 2 ^ j :=
    (Nat.mod_modEq 3 (2 ^ j)).mul_right x.val
  rw [hmul, ← Nat.add_mod]

theorem oddCount_affineThree_mod (j s : ℕ) :
    oddCount (3 * s + 2) j = oddCount ((3 * s + 2) % 2 ^ j) j := by
  let y := 3 * s + 2
  let x := y % 2 ^ j
  let c := y / 2 ^ j
  have hy : y = x + c * 2 ^ j := by
    calc
      y = y % 2 ^ j + 2 ^ j * (y / 2 ^ j) := (Nat.mod_add_div y (2 ^ j)).symm
      _ = x + c * 2 ^ j := by dsimp [x, c]; ring
  change oddCount y j = oddCount x j
  rw [hy, oddCount_add_mul_two_pow]

theorem tstep_iterate_affineThree_mod (j s : ℕ) :
    tstep^[j] (3 * s + 2) =
      tstep^[j] ((3 * s + 2) % 2 ^ j) +
        ((3 * s + 2) / 2 ^ j) * 3 ^ oddCount ((3 * s + 2) % 2 ^ j) j := by
  let y := 3 * s + 2
  let x := y % 2 ^ j
  let c := y / 2 ^ j
  have hy : y = x + c * 2 ^ j := by
    calc
      y = y % 2 ^ j + 2 ^ j * (y / 2 ^ j) := (Nat.mod_add_div y (2 ^ j)).symm
      _ = x + c * 2 ^ j := by dsimp [x, c]; ring
  change tstep^[j] y = tstep^[j] x + c * 3 ^ oddCount x j
  rw [hy, tstep_iterate_add_mul_two_pow]

theorem affineThreeNat_injective (j : ℕ) :
    Set.InjOn (fun s => (3 * s + 2) % 2 ^ j) (Finset.range (2 ^ j)) := by
  intro s hs t ht hst
  have hslt : s < 2 ^ j := Finset.mem_range.mp hs
  have htlt : t < 2 ^ j := Finset.mem_range.mp ht
  change (3 * s + 2) % 2 ^ j = (3 * t + 2) % 2 ^ j at hst
  have he : affineThreeEquiv j (s : ZMod (2 ^ j)) =
      affineThreeEquiv j (t : ZMod (2 ^ j)) := by
    apply ZMod.val_injective
    rw [affineThreeEquiv_val, affineThreeEquiv_val,
      ZMod.val_natCast_of_lt hslt, ZMod.val_natCast_of_lt htlt, hst]
  have hcast : (s : ZMod (2 ^ j)) = (t : ZMod (2 ^ j)) :=
    (affineThreeEquiv j).injective he
  have hval := congrArg ZMod.val hcast
  simpa [ZMod.val_natCast_of_lt hslt, ZMod.val_natCast_of_lt htlt] using hval

theorem affineThreeNat_surjective (j : ℕ) :
    Set.SurjOn (fun s => (3 * s + 2) % 2 ^ j)
      (Finset.range (2 ^ j)) (Finset.range (2 ^ j)) := by
  intro x hx
  have hxlt : x < 2 ^ j := Finset.mem_range.mp hx
  let q : ZMod (2 ^ j) := (affineThreeEquiv j).symm (x : ZMod (2 ^ j))
  refine ⟨q.val, Finset.mem_range.mpr (ZMod.val_lt q), ?_⟩
  have he : affineThreeEquiv j q = (x : ZMod (2 ^ j)) := by
    simp [q]
  have hval := congrArg ZMod.val he
  rw [affineThreeEquiv_val, ZMod.val_natCast_of_lt hxlt] at hval
  exact hval

theorem slicePhase_affineThree_mod {j a ξ s : ℕ}
    (ha : oddCount (3 * s + 2) j = a) :
    slicePhase (a + 1) (3 * ξ) (tstep^[j] (3 * s + 2)) =
      slicePhase a ξ (tstep^[j] ((3 * s + 2) % 2 ^ j)) := by
  rw [slicePhase_scale, tstep_iterate_affineThree_mod,
    ← oddCount_affineThree_mod j s, ha, slicePhase_add_mul_pow]

theorem sliceChar_odd_succ (j a ξ : ℕ) :
    (∑ s ∈ Finset.range (2 ^ j),
      if oddCount (3 * s + 2) j = a then
        slicePhase (a + 1) (3 * ξ) (tstep^[j] (3 * s + 2)) else 0) =
      sliceChar j a ξ := by
  rw [sliceChar_eq_sum_phase]
  apply Finset.sum_nbij (fun s => (3 * s + 2) % 2 ^ j)
  · intro s hs
    exact Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
  · exact affineThreeNat_injective j
  · exact affineThreeNat_surjective j
  · intro s hs
    rw [← oddCount_affineThree_mod j s]
    split_ifs with ha
    · exact slicePhase_affineThree_mod ha
    · rfl

/-- **Pascal recursion.**  The slice with one extra odd step splits into even starts, which keep
the modulus-`3^(a+1)` slice, and odd starts, whose affine images permute `ℤ/2^j`. -/
theorem sliceChar_pascal (j a ξ : ℕ) :
    sliceChar (j + 1) (a + 1) (3 * ξ) =
      sliceChar j (a + 1) (3 * ξ) + sliceChar j a ξ := by
  rw [sliceChar_succ_split, sliceChar_odd_succ]
  congr 1
  exact (sliceChar_eq_sum_phase j (a + 1) (3 * ξ)).symm

/-- The closed form obtained by iterating `sliceChar_pascal` through `k` powers of three.  The
index `t=s-1` is exactly the positive-time indexing; starting the sum at `s=0` would introduce a
spurious term when `k=1`. -/
noncomputable def subsliceSum (j a k u : ℕ) : ℂ :=
  ∑ t ∈ Finset.range j,
    (t.choose (k - 1) : ℂ) * sliceChar (j - 1 - t) (a - k) u

/-- **Sub-slice decomposition.**  A frequency divisible by `3^k` is the binomially weighted sum
of the slices seen immediately after the `k`-th odd step. -/
theorem sliceChar_eq_subsliceSum (j a k u : ℕ) (hk : 1 ≤ k) (hka : k ≤ a) :
    sliceChar j a (3 ^ k * u) = subsliceSum j a k u := by
  induction j generalizing a k with
  | zero =>
      have ha : a ≠ 0 := by omega
      have h0a : ¬ 0 = a := by omega
      simp [subsliceSum, sliceChar, levelSet, oddCount_zero, h0a]
  | succ j ih =>
      cases a with
      | zero => omega
      | succ a =>
          cases k with
          | zero => omega
          | succ k =>
              have hfreq : 3 ^ (k + 1) * u = 3 * (3 ^ k * u) := by
                rw [pow_succ']
                ring
              rw [hfreq, sliceChar_pascal, ← hfreq]
              cases k with
              | zero =>
                  simp only [pow_zero, one_mul]
                  rw [ih (a + 1) 1 (by omega) (by omega)]
                  simp only [subsliceSum, Nat.add_sub_cancel, Nat.reduceSubDiff,
                    Nat.choose_zero_right, Nat.cast_one, one_mul, Finset.sum_range_succ']
                  congr 1
                  apply Finset.sum_congr rfl
                  intro t ht
                  have htj : t < j := Finset.mem_range.mp ht
                  apply congrArg (fun n => sliceChar n a u)
                  omega
              | succ k =>
                  rw [ih (a + 1) (k + 2) (by omega) (by omega),
                    ih a (k + 1) (by omega) (by omega)]
                  unfold subsliceSum
                  rw [Finset.sum_range_succ']
                  rw [show k + 2 - 1 = k + 1 by omega,
                    show k + 1 - 1 = k by omega,
                    show a + 1 - (k + 2) = a - (k + 1) by omega]
                  simp only [Nat.choose_zero_succ, Nat.cast_zero, zero_mul, add_zero,
                    Nat.add_sub_cancel, Nat.sub_zero]
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro t ht
                  have htj : t < j := Finset.mem_range.mp ht
                  rw [show j - (t + 1) = j - 1 - t by omega, Nat.choose_succ_succ]
                  push_cast
                  ring

/-! ## Fourier expansion of least-residue parity -/

/-- The normalized Fourier coefficient of least-residue parity on `ℤ/(3^a)`. -/
noncomputable def gHatZ (a : ℕ) (ξ : ZMod (3 ^ a)) : ℂ :=
  ((3 ^ a : ℕ) : ℂ)⁻¹ * ∑ y : ZMod (3 ^ a),
    (paritySign y.val : ℂ) * ZMod.stdAddChar (-(ξ * y))

theorem slicePhase_eq_stdAddChar (a ξ y : ℕ) :
    slicePhase a ξ y = ZMod.stdAddChar ((ξ : ZMod (3 ^ a)) * (y : ZMod (3 ^ a))) := by
  rw [show (ξ : ZMod (3 ^ a)) * (y : ZMod (3 ^ a)) =
      ((ξ * y : ℕ) : ZMod (3 ^ a)) by norm_cast]
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold slicePhase
  push_cast
  rfl

/-- The exponential in `sliceChar` is mathlib's standard additive character. -/
theorem sliceChar_eq_zmod_sum (j a ξ : ℕ) :
    sliceChar j a ξ = ∑ r ∈ levelSet j a,
      ZMod.stdAddChar ((ξ : ZMod (3 ^ a)) * (tstep^[j] r : ZMod (3 ^ a))) := by
  rw [sliceChar_eq_sum_phase]
  unfold levelSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs
  · exact slicePhase_eq_stdAddChar a ξ (tstep^[j] r)
  · rfl

/-- Fourier inversion on the odd cyclic group `ℤ/(3^a)`, in the normalization used by `gHatZ`. -/
theorem zmod_fourier_inversion (a : ℕ) (f : ZMod (3 ^ a) → ℂ) (y : ZMod (3 ^ a)) :
    ∑ ξ : ZMod (3 ^ a),
      (((3 ^ a : ℕ) : ℂ)⁻¹ * ∑ z : ZMod (3 ^ a),
        f z * ZMod.stdAddChar (-(ξ * z))) * ZMod.stdAddChar (ξ * y) = f y := by
  let M := 3 ^ a
  have hM : (M : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero a (by norm_num : (3 : ℕ) ≠ 0))
  have horth (z : ZMod M) :
      ∑ ξ : ZMod M, ZMod.stdAddChar (ξ * (y - z)) =
        if y = z then (M : ℂ) else 0 := by
    rw [AddChar.sum_mulShift (y - z) (ZMod.isPrimitive_stdAddChar M)]
    simp [sub_eq_zero, ZMod.card, M]
  change ∑ ξ : ZMod M,
      ((M : ℂ)⁻¹ * ∑ z : ZMod M, f z * ZMod.stdAddChar (-(ξ * z))) *
        ZMod.stdAddChar (ξ * y) = f y
  calc
    _ = ∑ z : ZMod M, ∑ ξ : ZMod M,
          (M : ℂ)⁻¹ * (f z * ZMod.stdAddChar (-(ξ * z))) *
            ZMod.stdAddChar (ξ * y) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = (M : ℂ)⁻¹ * ∑ z : ZMod M, f z *
          ∑ ξ : ZMod M, ZMod.stdAddChar (ξ * (y - z)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ hξ
      have hc : ZMod.stdAddChar (-(ξ * z)) * ZMod.stdAddChar (ξ * y) =
          ZMod.stdAddChar (ξ * (y - z)) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      rw [show (M : ℂ)⁻¹ * (f z * ZMod.stdAddChar (-(ξ * z))) *
          ZMod.stdAddChar (ξ * y) =
          (M : ℂ)⁻¹ * f z *
            (ZMod.stdAddChar (-(ξ * z)) * ZMod.stdAddChar (ξ * y)) by ring, hc]
      ring
    _ = (M : ℂ)⁻¹ * ((M : ℂ) * f y) := by
      congr 1
      simp_rw [horth]
      simp
      ring
    _ = f y := by field_simp

/-- **Fourier identity.**  Since every slice iterate is the least representative below `3^a`,
Fourier inversion of least-residue parity turns the signed slice count into its complete family
of slice characters. -/
theorem levelSign_eq_fourier_slice (j a : ℕ) :
    (levelSign j a : ℂ) =
      ∑ ξ : ZMod (3 ^ a), gHatZ a ξ * sliceChar j a ξ.val := by
  rw [show (levelSign j a : ℂ) =
      ∑ r ∈ levelSet j a, (paritySign (tstep^[j] r) : ℂ) by
    unfold levelSign
    push_cast
    apply Finset.sum_congr rfl
    intro r hr
    rw [paritySign_eq_ite]
    split_ifs <;> norm_num]
  simp_rw [sliceChar_eq_zmod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  unfold gHatZ
  have hinv := zmod_fourier_inversion a (fun y => (paritySign y.val : ℂ))
    (tstep^[j] r : ZMod (3 ^ a))
  have hlt : tstep^[j] r < 3 ^ a := by
    have h := tstep_iterate_lt_three_pow
      (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
    simpa [(Finset.mem_filter.mp hr).2] using h
  rw [ZMod.val_natCast_of_lt hlt] at hinv
  simpa only [ZMod.natCast_zmod_val] using hinv.symm

/-- **Edge: slice character decay gives C1 directly** (no fine-scale mixing, no Tao §6).  Proof owed,
plan in the module docstring.  With `sliceCharDecay_of_pascalDampingDecay` (SliceSeven.lean) this
makes `BiasDecays` follow from `PascalDampingDecay` alone.  Confidence 75%. -/
theorem biasDecays_of_sliceCharDecay (h : SliceCharDecay) : BiasDecays := by
  sorry

end CollatzMoonshot.Conjugacy
