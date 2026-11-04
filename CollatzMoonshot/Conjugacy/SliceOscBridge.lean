/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.BeyondWordsLinear
import TaoCollatz.Fourier.ZMod3
import TaoCollatz.Sec6.MixingCore

/-!
# The slice oscillation is Tao's oscillation of the slice density

`levelOsc j a m` (`Bridge3.lean`) is written on least residues `y < 3^a` with counts.  Tao's
functional `TaoCollatz.osc m a hma c` (`Fourier/ZMod3.lean`, paper (1.24)) is written on
`ZMod (3^a)` with fibres of `ZMod (3^a) → ZMod (3^m)`.  Every iterate of a `j`-bit start with
`a` odd steps lies below `3^a` (`tstep_iterate_lt_three_pow`), so the slice law is a density
on `ZMod (3^a)`, and the two functionals agree exactly (`levelOsc_eq_osc`).  This is item (i)
of `SEC6S-PLAN.md`: every `Sec6` statement about `osc` of a density applies verbatim to the
slice laws.
-/

namespace CollatzMoonshot.Conjugacy

open CollatzMoonshot.FrontB

/-- The slice law at `(j, a)` as an (unnormalised, counting) density on `ZMod (3^a)`. -/
noncomputable def sliceDensity (j a : ℕ) : ZMod (3 ^ a) → ℝ := fun Y => levelMass j a Y.val

/-- Summing over `ZMod (3^a)` is summing over least residues `y < 3^a`. -/
theorem sum_zmod_three_pow_eq_sum_range (a : ℕ) (f : ℕ → ℝ) :
    ∑ Y : ZMod (3 ^ a), f Y.val = ∑ y ∈ Finset.range (3 ^ a), f y := by
  have : NeZero (3 ^ a) := ⟨by positivity⟩
  refine Finset.sum_nbij' (fun Y => Y.val) (fun y => (y : ZMod (3 ^ a))) ?_ ?_ ?_ ?_ ?_
  · intro Y _
    exact Finset.mem_range.2 (ZMod.val_lt Y)
  · intro y _
    exact Finset.mem_univ _
  · intro Y _
    exact ZMod.natCast_zmod_val Y
  · intro y hy
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hy)]
  · intro Y _
    rfl

/-- The slice class mod `3^m` is the sum of the slice masses over the residues in that class. -/
theorem levelClass_eq_sum_mass (j a m c : ℕ) :
    (levelClass j a m c : ℝ) =
      ∑ y ∈ Finset.range (3 ^ a), if y % 3 ^ m = c then (levelMass j a y : ℝ) else 0 := by
  have h := sum_levelSet_eq_sum_mass j a (fun y => if y % 3 ^ m = c then (1 : ℂ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_boole] at h
  have h' : ((levelClass j a m c : ℝ) : ℂ) =
      ((∑ y ∈ Finset.range (3 ^ a),
        if y % 3 ^ m = c then (levelMass j a y : ℝ) else 0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Complex.ofReal_natCast]
    simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_natCast, Complex.ofReal_zero]
    exact h
  exact_mod_cast h'

/-- Two residues mod `3^a` have the same image mod `3^m` iff their least residues agree
mod `3^m`. -/
theorem castHom_eq_iff_val_mod (a m : ℕ) (hma : m ≤ a) (Y Y' : ZMod (3 ^ a)) :
    ZMod.castHom (pow_dvd_pow 3 hma) (ZMod (3 ^ m)) Y' =
        ZMod.castHom (pow_dvd_pow 3 hma) (ZMod (3 ^ m)) Y ↔
      Y'.val % 3 ^ m = Y.val % 3 ^ m := by
  have : NeZero (3 ^ a) := ⟨by positivity⟩
  rw [ZMod.castHom_apply, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.cast_eq_val,
    ZMod.natCast_eq_natCast_iff']

/-- **The bridge.**  The slice oscillation above scale `m` is Tao's `osc m a` of the slice
density: `levelOsc j a m = osc m a hma (sliceDensity j a)`. -/
theorem levelOsc_eq_osc (j a m : ℕ) (hma : m ≤ a) :
    levelOsc j a m = TaoCollatz.osc m a hma (sliceDensity j a) := by
  have : NeZero (3 ^ a) := ⟨by positivity⟩
  have hfib (Y : ZMod (3 ^ a)) :
      ∑ Y' ∈ Finset.univ.filter (fun Y' : ZMod (3 ^ a) =>
          ZMod.castHom (pow_dvd_pow 3 hma) (ZMod (3 ^ m)) Y'
            = ZMod.castHom (pow_dvd_pow 3 hma) (ZMod (3 ^ m)) Y), sliceDensity j a Y' =
        (levelClass j a m (Y.val % 3 ^ m) : ℝ) := by
    rw [Finset.sum_filter, levelClass_eq_sum_mass]
    rw [← sum_zmod_three_pow_eq_sum_range a
      (fun y => if y % 3 ^ m = Y.val % 3 ^ m then (levelMass j a y : ℝ) else 0)]
    apply Finset.sum_congr rfl
    intro Y' _
    simp only [castHom_eq_iff_val_mod a m hma Y Y', sliceDensity]
  have hpow : (3 : ℝ) ^ ((m : ℤ) - (a : ℤ)) = (3 : ℝ) ^ m / 3 ^ a := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
  unfold TaoCollatz.osc levelOsc
  simp only [hfib, hpow]
  exact (sum_zmod_three_pow_eq_sum_range a (fun y =>
    |(levelMass j a y : ℝ) - (3 : ℝ) ^ m / 3 ^ a * levelClass j a m (y % 3 ^ m)|)).symm

/-- The slice oscillation is at most twice the slice size (`TaoCollatz.osc_le_two_mul_l1`
through the bridge). -/
theorem levelOsc_le_two_mul_card (j a m : ℕ) (hma : m ≤ a) :
    levelOsc j a m ≤ 2 * (levelSet j a).card := by
  rw [levelOsc_eq_osc j a m hma]
  refine (TaoCollatz.osc_le_two_mul_l1 m a hma _).trans ?_
  have h := sum_levelSet_eq_sum_mass j a (fun _ => (1 : ℂ))
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  have hsum : ∑ Y : ZMod (3 ^ a), |sliceDensity j a Y| = (levelSet j a).card := by
    simp only [sliceDensity, Nat.abs_cast]
    calc
      ∑ Y : ZMod (3 ^ a), (levelMass j a Y.val : ℝ) =
          ∑ y ∈ Finset.range (3 ^ a), (levelMass j a y : ℝ) :=
        sum_zmod_three_pow_eq_sum_range a (fun y => (levelMass j a y : ℝ))
      _ = (levelSet j a).card := by exact_mod_cast h.symm
  rw [hsum]

end CollatzMoonshot.Conjugacy
