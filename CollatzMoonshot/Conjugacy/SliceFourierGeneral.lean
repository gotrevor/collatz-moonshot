/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.SliceFourier

/-!
# The slice-Fourier pipeline for an arbitrary least-residue observable (2026-11-04)

`SliceFourier.lean` proves C1 by expanding least-residue parity `(−1)^y` on `[0, 3^a)` in additive
characters of `ℤ/3^a`.  Nothing in that argument used the specific observable except its Fourier
weights: the total weight `O(a)` and the layered weights `O(3^{−k} a)` on frequencies divisible by
`3^k`.  This file runs the same pipeline for any `f : ℕ → ℂ`, read on least residues.

* `resFourier a f`: the normalised Fourier transform of `y ↦ f y.val` on `ℤ/3^a`.
* `sum_levelSet_eq_fourier_slice`: the slice sum `Σ_{r ∈ levelSet j a} f (T^j r)` is
  `Σ_ξ resFourier a f ξ · sliceChar j a ξ.val` (Fourier inversion; `T^j r < 3^a` on the slice).
* `LayeredWeight a f W`: the weight on `{ξ : 3^k ∣ ξ.val}` is at most `3^{−k} W`, for `k ≤ a`.
* `eventually_norm_levelSum_le`: under `SliceCharDecay`, an observable whose layered weight is
  `B · 4(a+1)` has central slice sums `≤ ε · #slice`, eventually and uniformly in the observable.
* `norm_sum_range_le_of_levelSum`: summing over the slices, with the non-central ones bounded by
  their cardinality (`outOddSet`).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-! ## Fourier expansion of an arbitrary observable -/

/-- The normalized Fourier coefficient on `ℤ/(3^a)` of the observable `f`, read on least
residues. -/
noncomputable def resFourier (a : ℕ) (f : ℕ → ℂ) (ξ : ZMod (3 ^ a)) : ℂ :=
  ((3 ^ a : ℕ) : ℂ)⁻¹ * ∑ y : ZMod (3 ^ a), f y.val * ZMod.stdAddChar (-(ξ * y))

/-- **Fourier identity for an arbitrary observable.**  The slice sum of `f ∘ T^j` is the
`resFourier`-weighted family of slice characters, exactly as `levelSign_eq_fourier_slice`. -/
theorem sum_levelSet_eq_fourier_slice (j a : ℕ) (f : ℕ → ℂ) :
    ∑ r ∈ levelSet j a, f (tstep^[j] r) =
      ∑ ξ : ZMod (3 ^ a), resFourier a f ξ * sliceChar j a ξ.val := by
  simp_rw [sliceChar_eq_zmod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  unfold resFourier
  have hinv := zmod_fourier_inversion a (fun y => f y.val) (tstep^[j] r : ZMod (3 ^ a))
  have hlt : tstep^[j] r < 3 ^ a := by
    have h := tstep_iterate_lt_three_pow
      (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
    simpa [(Finset.mem_filter.mp hr).2] using h
  rw [ZMod.val_natCast_of_lt hlt] at hinv
  simpa only [ZMod.natCast_zmod_val] using hinv.symm

/-- The layered Fourier-weight hypothesis: frequencies divisible by `3^k` carry total weight at
most `3^{−k} W`.  At `k = 0` this is the total weight bound `Σ_ξ ‖f̂ ξ‖ ≤ W`. -/
def LayeredWeight (a : ℕ) (f : ℕ → ℂ) (W : ℝ) : Prop :=
  ∀ k ≤ a, (∑ ξ : ZMod (3 ^ a), if 3 ^ k ∣ ξ.val then ‖resFourier a f ξ‖ else 0) ≤
    ((3 : ℝ) ^ k)⁻¹ * W

/-- The parity observable has layered weight `4(a+1)` (`sum_norm_gHatZ_dvd_le`). -/
theorem layeredWeight_paritySign (a : ℕ) :
    LayeredWeight a (fun y => (paritySign y : ℂ)) (4 * (a + 1)) := by
  intro k hk
  have hcoef : resFourier a (fun y => (paritySign y : ℂ)) = gHatZ a := by
    funext ξ
    rfl
  rw [hcoef]
  exact sum_norm_gHatZ_dvd_le a k hk

/-! ## The uniform central-slice bound -/

/-- **Generic central-slice bound.**  Fourier inversion plus the valuation split turns the
low-frequency slice estimate into a bound on the slice sum of every observable with layered
weight `B · 4(a+1)`, with the same majorant as `exists_abs_levelSign_le` scaled by `B`. -/
theorem exists_norm_levelSum_le (h : SliceCharDecay) :
    ∃ C > (0 : ℝ), ∀ j a : ℕ, 4096 ≤ j → j ≤ 4 * a → a ≤ 11 * j / 20 →
      ∀ (f : ℕ → ℂ) (B : ℝ), LayeredWeight a f (B * (4 * (a + 1))) →
      ‖∑ r ∈ levelSet j a, f (tstep^[j] r)‖ ≤
        B * (((4 * C / (j : ℝ) ^ 2 +
            (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)) * (4 * (a + 1)) +
          ((3 : ℝ) ^ (j / 4096))⁻¹ * (4 * (a + 1))) * (levelSet j a).card) := by
  obtain ⟨C, hCpos, hlow⟩ := exists_norm_sliceChar_pow_le h
  refine ⟨C, hCpos, fun j a hj hja haj f B hf => ?_⟩
  let K := j / 4096
  let E := 4 * C / (j : ℝ) ^ 2 +
    (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)
  let g := resFourier a f
  have hKpos : 1 ≤ K := by dsimp [K]; omega
  have hKa : K ≤ a := by dsimp [K]; omega
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlowξ (ξ : ZMod (3 ^ a)) (hξ : ¬3 ^ K ∣ ξ.val) :
      ‖sliceChar j a ξ.val‖ ≤ E * (levelSet j a).card := by
    have hξ0 : ξ.val ≠ 0 := by
      intro hz
      apply hξ
      rw [hz]
      exact dvd_zero _
    let k := padicValNat 3 ξ.val
    let u := ξ.val.divMaxPow 3
    have hku : 3 ^ k * u = ξ.val := by
      exact Nat.pow_padicValNat_mul_divMaxPow 3 ξ.val
    have hu : ¬3 ∣ u := by
      exact Nat.not_dvd_divMaxPow (by norm_num) hξ0
    have hkK : k < K := by
      by_contra hnot
      apply hξ
      exact (Nat.pow_dvd_pow 3 (Nat.le_of_not_gt hnot)).trans pow_padicValNat_dvd
    have hjk : 4096 * k ≤ j := by
      dsimp [K] at hkK
      omega
    have hb := hlow j a k u (by omega) hja haj hjk hu
    rw [hku] at hb
    rw [card_levelSet_eq_choose]
    simpa [E] using hb
  have hpoint (ξ : ZMod (3 ^ a)) :
      ‖g ξ * sliceChar j a ξ.val‖ ≤
        E * (levelSet j a).card * ‖g ξ‖ +
          if 3 ^ K ∣ ξ.val then (levelSet j a).card * ‖g ξ‖ else 0 := by
    rw [norm_mul]
    by_cases hξ : 3 ^ K ∣ ξ.val
    · rw [if_pos hξ]
      have ht := norm_sliceChar_le_card j a ξ.val
      have hg : 0 ≤ ‖g ξ‖ := norm_nonneg _
      have hc : (0 : ℝ) ≤ (levelSet j a).card := by positivity
      have hmain : ‖g ξ‖ * ‖sliceChar j a ξ.val‖ ≤
          ‖g ξ‖ * (levelSet j a).card :=
        mul_le_mul_of_nonneg_left ht hg
      nlinarith [mul_nonneg hE (mul_nonneg hc hg)]
    · rw [if_neg hξ]
      have hb := hlowξ ξ hξ
      calc
        ‖g ξ‖ * ‖sliceChar j a ξ.val‖ ≤
            ‖g ξ‖ * (E * (levelSet j a).card) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = E * (levelSet j a).card * ‖g ξ‖ + 0 := by ring
  have hsum :
      ‖∑ r ∈ levelSet j a, f (tstep^[j] r)‖ ≤
        E * (levelSet j a).card * (∑ ξ : ZMod (3 ^ a), ‖g ξ‖) +
          (levelSet j a).card *
            (∑ ξ : ZMod (3 ^ a), if 3 ^ K ∣ ξ.val then ‖g ξ‖ else 0) := by
    calc
      ‖∑ r ∈ levelSet j a, f (tstep^[j] r)‖ =
          ‖∑ ξ : ZMod (3 ^ a), g ξ * sliceChar j a ξ.val‖ := by
        rw [sum_levelSet_eq_fourier_slice]
      _ ≤ ∑ ξ : ZMod (3 ^ a), ‖g ξ * sliceChar j a ξ.val‖ :=
        norm_sum_le _ _
      _ ≤ ∑ ξ : ZMod (3 ^ a),
          (E * (levelSet j a).card * ‖g ξ‖ +
            if 3 ^ K ∣ ξ.val then (levelSet j a).card * ‖g ξ‖ else 0) := by
        exact Finset.sum_le_sum fun ξ _ => hpoint ξ
      _ = E * (levelSet j a).card * (∑ ξ : ZMod (3 ^ a), ‖g ξ‖) +
          (levelSet j a).card *
            (∑ ξ : ZMod (3 ^ a), if 3 ^ K ∣ ξ.val then ‖g ξ‖ else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro ξ hξ
        split_ifs <;> ring
  have hall : (∑ ξ : ZMod (3 ^ a), ‖g ξ‖) ≤ B * (4 * (a + 1)) := by
    have h0 := hf 0 (Nat.zero_le a)
    simpa using h0
  have hhigh := hf K hKa
  have hcard : (0 : ℝ) ≤ (levelSet j a).card := by positivity
  calc
    ‖∑ r ∈ levelSet j a, f (tstep^[j] r)‖ ≤
        E * (levelSet j a).card * (∑ ξ : ZMod (3 ^ a), ‖g ξ‖) +
          (levelSet j a).card *
            (∑ ξ : ZMod (3 ^ a), if 3 ^ K ∣ ξ.val then ‖g ξ‖ else 0) := hsum
    _ ≤ E * (levelSet j a).card * (B * (4 * (a + 1))) +
          (levelSet j a).card * (((3 : ℝ) ^ K)⁻¹ * (B * (4 * (a + 1)))) := by
      gcongr
    _ = B * ((E * (4 * (a + 1)) + ((3 : ℝ) ^ K)⁻¹ * (4 * (a + 1))) *
          (levelSet j a).card) := by ring

/-- **Generic central-slice negligibility.**  For a fixed weight constant `B`, eventually every
central slice sum of every observable with layered weight `B · 4(a+1)` is `≤ ε · #slice`. -/
theorem eventually_norm_levelSum_le (h : SliceCharDecay) (B : ℝ) (hB : 0 ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ a : ℕ, j ≤ 4 * a → a ≤ 11 * j / 20 →
      ∀ f : ℕ → ℂ, LayeredWeight a f (B * (4 * (a + 1))) →
      ‖∑ r ∈ levelSet j a, f (tstep^[j] r)‖ ≤ ε * (levelSet j a).card := by
  obtain ⟨C, hCpos, hsign⟩ := exists_norm_levelSum_le h
  have hlim : Tendsto (fun j => B * sliceFourierMajorant C j) atTop (𝓝 0) := by
    simpa using (tendsto_sliceFourierMajorant C hCpos.le).const_mul B
  have hsmall : ∀ᶠ j in atTop, B * sliceFourierMajorant C j < ε :=
    hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall, eventually_ge_atTop 4096] with j hjε hj
  intro a hja haj f hf
  have haj' : a ≤ j := by omega
  have hbound := hsign j a hj hja haj f B hf
  have hE : 0 ≤ 4 * C / (j : ℝ) ^ 2 +
      (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32) := by positivity
  have hhigh : 0 ≤ ((3 : ℝ) ^ (j / 4096))⁻¹ := by positivity
  have hacast : (a + 1 : ℕ) ≤ (j + 1 : ℕ) := Nat.add_le_add_right haj' 1
  have hcoef :
      (4 * C / (j : ℝ) ^ 2 +
          (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)) * (4 * (a + 1)) +
        ((3 : ℝ) ^ (j / 4096))⁻¹ * (4 * (a + 1)) ≤
        sliceFourierMajorant C j := by
    unfold sliceFourierMajorant
    have hacastR : ((a + 1 : ℕ) : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast hacast
    gcongr
  have hcard : (0 : ℝ) ≤ (levelSet j a).card := by positivity
  calc
    ‖∑ r ∈ levelSet j a, f (tstep^[j] r)‖ ≤
        B * (((4 * C / (j : ℝ) ^ 2 +
            (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)) * (4 * (a + 1)) +
          ((3 : ℝ) ^ (j / 4096))⁻¹ * (4 * (a + 1))) * (levelSet j a).card) := hbound
    _ ≤ B * (sliceFourierMajorant C j * (levelSet j a).card) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef hcard) hB
    _ = (B * sliceFourierMajorant C j) * (levelSet j a).card := by ring
    _ ≤ ε * (levelSet j a).card :=
      mul_le_mul_of_nonneg_right hjε.le hcard

/-! ## Summing over the slices -/

/-- The slices partition the `j`-bit starts, for any observable. -/
theorem sum_range_eq_sum_levelSet (j : ℕ) (g : ℕ → ℂ) :
    ∑ r ∈ Finset.range (2 ^ j), g r =
      ∑ a ∈ Finset.range (j + 1), ∑ r ∈ levelSet j a, g r := by
  unfold levelSet
  rw [Finset.sum_fiberwise_of_maps_to]
  intro r _
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (oddCount_le r j))

/-- Sum a uniform central-slice bound for an observable bounded by `1`, and control the
complementary slices by their cardinality, as in `abs_bias_le_of_levelSign`. -/
theorem norm_sum_range_le_of_levelSum (j : ℕ) (f : ℕ → ℂ) (hf1 : ∀ y, ‖f y‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hslice : ∀ a, j ≤ 4 * a → a ≤ 11 * j / 20 →
      ‖∑ r ∈ levelSet j a, f (tstep^[j] r)‖ ≤ ε * (levelSet j a).card) :
    ‖∑ r ∈ Finset.range (2 ^ j), f (tstep^[j] r)‖ ≤ ε * 2 ^ j + (outOddSet j).card := by
  let I := Finset.range (j + 1)
  let L := I.filter (fun a => j ≤ 4 * a ∧ a ≤ 11 * j / 20)
  let H := I.filter (fun a => 4 * a < j ∨ 11 * j / 20 < a)
  let S : ℕ → ℂ := fun a => ∑ r ∈ levelSet j a, f (tstep^[j] r)
  have hLcard : ∑ a ∈ L, ((levelSet j a).card : ℝ) ≤ 2 ^ j := by
    calc
      ∑ a ∈ L, ((levelSet j a).card : ℝ) ≤
          ∑ a ∈ I, ((levelSet j a).card : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = 2 ^ j := by
        exact_mod_cast sum_levelSet_card j
  have hlow : ‖∑ a ∈ L, S a‖ ≤ ε * 2 ^ j := by
    calc
      ‖∑ a ∈ L, S a‖ ≤ ∑ a ∈ L, ‖S a‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ L, ε * (levelSet j a).card := by
        exact Finset.sum_le_sum fun a ha => hslice a
          (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
      _ = ε * ∑ a ∈ L, ((levelSet j a).card : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ε * 2 ^ j := mul_le_mul_of_nonneg_left hLcard hε
  have hHcard : ∑ a ∈ H, ((levelSet j a).card : ℝ) = (outOddSet j).card := by
    exact_mod_cast sum_out_levelSet_card j
  have hcardS (a : ℕ) : ‖S a‖ ≤ (levelSet j a).card := by
    calc
      ‖S a‖ ≤ ∑ r ∈ levelSet j a, ‖f (tstep^[j] r)‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ levelSet j a, (1 : ℝ) := Finset.sum_le_sum fun r _ => hf1 _
      _ = (levelSet j a).card := by simp
  have hhigh : ‖∑ a ∈ H, S a‖ ≤ (outOddSet j).card := by
    calc
      ‖∑ a ∈ H, S a‖ ≤ ∑ a ∈ H, ‖S a‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ H, ((levelSet j a).card : ℝ) :=
        Finset.sum_le_sum fun a _ => hcardS a
      _ = (outOddSet j).card := hHcard
  have hpartition : ∑ a ∈ I, S a = (∑ a ∈ L, S a) + ∑ a ∈ H, S a := by
    have hs := Finset.sum_filter_add_sum_filter_not I
      (fun a => j ≤ 4 * a ∧ a ≤ 11 * j / 20) S
    rw [show I.filter (fun a => ¬(j ≤ 4 * a ∧ a ≤ 11 * j / 20)) = H by
      ext a
      simp [H]
      omega] at hs
    exact hs.symm
  rw [sum_range_eq_sum_levelSet j (fun r => f (tstep^[j] r))]
  change ‖∑ a ∈ I, S a‖ ≤ _
  rw [hpartition]
  exact (norm_add_le _ _).trans (add_le_add hlow hhigh)

end CollatzMoonshot.Conjugacy
