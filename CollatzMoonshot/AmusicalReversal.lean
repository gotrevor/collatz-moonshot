/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Time reversal: the mechanism the amusical permutation lacks

From the 2026-10-13 "relative" research agent.  A permutation `σ` with a reversing involution
`ι` (`ι σ ι = σ⁻¹`) has each orbit meeting `Fix ι` in at most two points, so an infinite fixed
set forces infinitely many orbits.  The Gaussian relative in `GaussianRelative.lean` has
complex conjugation as such a reversor.  For `U`:

* Klamkin's problem (a) is *equivalent* to the existence of a reversing involution of `U` with
  infinitely many nonnegative fixed points (`infinitelyManyOrbits_iff_reversor`), so a reversor
  is a costume of the problem in general;
* but **no reversor is affine on finitely many pieces** (`no_piecewiseAffine_reversor`): every
  step of `U` adds `1` to the `3`-adic valuation of the slope and every step of `U⁻¹` removes
  one, and a piecewise-affine conjugacy changes valuations by a bounded amount.  `ℚ` has no
  automorphism exchanging `2` and `3`; in `ℤ[i]` conjugation exchanges `2 + i` and `2 − i`.

Treadmill target (`KICKOFF-2026-10-13-amusical-reversal.md`): close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

private lemma dvd_of_dvd_two_mul_pair {p d e : ℤ} (hd : p ∣ 2 * d) (he : p ∣ 2 * e) :
    p ∣ d ∨ p ∣ e ∨ p ∣ e - d := by
  rcases hd with ⟨q, hq⟩
  rcases he with ⟨r, hr⟩
  rcases Int.even_or_odd' q with ⟨s, hs | hs⟩
  · left
    refine ⟨s, ?_⟩
    have h : 2 * d = 2 * (p * s) := by rw [hq, hs]; ring
    exact Int.eq_of_mul_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0) h
  rcases Int.even_or_odd' r with ⟨t, ht | ht⟩
  · right; left
    refine ⟨t, ?_⟩
    have h : 2 * e = 2 * (p * t) := by rw [hr, ht]; ring
    exact Int.eq_of_mul_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0) h
  · right; right
    refine ⟨t - s, ?_⟩
    have h : 2 * e - 2 * d = p * (2 * t + 1) - p * (2 * s + 1) := by rw [hq, hr, hs, ht]
    have h' : 2 * (e - d) = 2 * (p * (t - s)) := by
      calc
        2 * (e - d) = 2 * e - 2 * d := by ring
        _ = p * (2 * t + 1) - p * (2 * s + 1) := h
        _ = 2 * (p * (t - s)) := by ring
    exact Int.eq_of_mul_eq_mul_left (by norm_num : (2 : ℤ) ≠ 0) h'

/-- **The reversal lemma.**  If `ι` is an involution reversing `σ` and both `x` and `σ^k x` are
fixed by `ι`, then `σ^(2k) x = x`. -/
theorem reversing_zpow_fixed {α : Type*} {σ ι : Equiv.Perm α} (hι : ι * ι = 1)
    (hrev : ι * σ * ι = σ⁻¹) {x : α} (hx : ι x = x) {k : ℤ} (hk : ι ((σ ^ k) x) = (σ ^ k) x) :
    (σ ^ (2 * k)) x = x := by
  have hinv : ι⁻¹ = ι := (eq_inv_of_mul_eq_one_left hι).symm
  -- conjugation by `ι` is a group hom, so it reverses every power
  have hpow : ι * σ ^ k * ι = σ ^ (-k) := by
    have := map_zpow (MulAut.conj ι) σ k
    simp only [MulAut.conj_apply, hinv] at this
    rw [this, hrev, inv_zpow', zpow_neg]
  have h1 : (σ ^ k) x = (σ ^ (-k)) x := by
    calc (σ ^ k) x = ι ((σ ^ k) x) := hk.symm
      _ = ι ((σ ^ k) (ι x)) := by rw [hx]
      _ = (ι * σ ^ k * ι) x := rfl
      _ = (σ ^ (-k)) x := by rw [hpow]
  calc (σ ^ (2 * k)) x = (σ ^ k) ((σ ^ k) x) := by rw [two_mul, zpow_add, Equiv.Perm.mul_apply]
    _ = (σ ^ k) ((σ ^ (-k)) x) := by rw [← h1]
    _ = x := by rw [← Equiv.Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero]; rfl

/-- **Target.**  An orbit of a reversible permutation meets the fixed set of the reversor in at
most two points (at most one if the orbit is infinite; `k ≡ 0, p/2 (mod p)` on a `p`-cycle). -/
theorem orbit_inter_fixedPoints_ncard_le_two {α : Type*} {σ ι : Equiv.Perm α}
    (hι : ι * ι = 1) (hrev : ι * σ * ι = σ⁻¹) (x : α) :
    (Set.range (fun k : ℤ => (σ ^ k) x) ∩ Function.fixedPoints ι).ncard ≤ 2 := by
  classical
  let S := Set.range (fun k : ℤ => (σ ^ k) x) ∩ Function.fixedPoints ι
  by_cases hS : S.Finite
  · by_contra hle
    have hlt : 2 < S.ncard := Nat.lt_of_not_ge hle
    rcases (Set.two_lt_ncard_iff hS).mp hlt with
      ⟨u, v, w, ⟨⟨ku, rfl⟩, hu⟩, ⟨⟨kv, rfl⟩, hv⟩, ⟨⟨kw, rfl⟩, hw⟩,
        huv, huw, hvw⟩
    have huv' : (σ ^ (kv - ku)) ((σ ^ ku) x) = (σ ^ kv) x := by
      rw [← Equiv.Perm.mul_apply, ← zpow_add]
      congr 2
      omega
    have huw' : (σ ^ (kw - ku)) ((σ ^ ku) x) = (σ ^ kw) x := by
      rw [← Equiv.Perm.mul_apply, ← zpow_add]
      congr 2
      omega
    have hv' : ι ((σ ^ (kv - ku)) ((σ ^ ku) x)) = (σ ^ (kv - ku)) ((σ ^ ku) x) := by
      rw [huv']; exact hv
    have hw' : ι ((σ ^ (kw - ku)) ((σ ^ ku) x)) = (σ ^ (kw - ku)) ((σ ^ ku) x) := by
      rw [huw']; exact hw
    have hdu := reversing_zpow_fixed hι hrev hu hv'
    have hdw := reversing_zpow_fixed hι hrev hu hw'
    let p := Function.minimalPeriod (fun y => σ • y) ((σ ^ ku) x)
    have hdu' : (p : ℤ) ∣ 2 * (kv - ku) :=
      MulAction.zpow_smul_eq_iff_minimalPeriod_dvd.mp (show
        (σ ^ (2 * (kv - ku))) • ((σ ^ ku) x) = (σ ^ ku) x from hdu)
    have hdw' : (p : ℤ) ∣ 2 * (kw - ku) :=
      MulAction.zpow_smul_eq_iff_minimalPeriod_dvd.mp (show
        (σ ^ (2 * (kw - ku))) • ((σ ^ ku) x) = (σ ^ ku) x from hdw)
    rcases dvd_of_dvd_two_mul_pair hdu' hdw' with h | h | h
    · have hh := MulAction.zpow_smul_eq_iff_minimalPeriod_dvd.mpr h
      exact huv (hh.symm.trans huv')
    · have hh := MulAction.zpow_smul_eq_iff_minimalPeriod_dvd.mpr h
      exact huw (hh.symm.trans huw')
    · rw [show kw - ku - (kv - ku) = kw - kv by omega] at h
      have hh := MulAction.zpow_smul_eq_iff_minimalPeriod_dvd.mpr h
      change (σ ^ (kw - kv)) ((σ ^ ku) x) = (σ ^ ku) x at hh
      apply hvw
      calc
        (σ ^ kv) x = (σ ^ (kv - ku)) ((σ ^ ku) x) := huv'.symm
        _ = (σ ^ (kv - ku)) ((σ ^ (kw - kv)) ((σ ^ ku) x)) := by rw [hh]
        _ = (σ ^ (kw - ku)) ((σ ^ ku) x) := by
          rw [← Equiv.Perm.mul_apply, ← zpow_add]
          congr 1
          ring
        _ = (σ ^ kw) x := huw'
  · rw [Set.Infinite.ncard hS]
    omega

/-- **Target.**  Klamkin's problem (a) is equivalent to the existence of a sign-preserving
reversing involution of `U` with infinitely many nonnegative fixed points.  (`⇐`: the orbit
count lemma above.  `⇒`: on each orbit `(x_k)` with chosen base point, set `ι x_k = x_{-k}`.) -/
theorem infinitelyManyOrbits_iff_reversor :
    AmusicalInfinitelyManyOrbits ↔ ∃ ι : Equiv.Perm ℤ, ι * ι = 1 ∧
      ι * amusicalPerm * ι = amusicalPerm⁻¹ ∧ (∀ x, 0 ≤ ι x ↔ 0 ≤ x) ∧
      {x : ℤ | 0 ≤ x ∧ ι x = x}.Infinite := by
  sorry

/-- **Target (Theorem NR).**  No bijection of `ℤ` that is affine with rational slope on each of
finitely many pieces (`c · ι x = a · x + b` on piece `j`) conjugates `U` to `U⁻¹`.  Paper proof:
`ι U^ℓ = U^{-ℓ} ι`; refine `ℤ` into finitely many cells (the piece of `n`, the residue class of
`n` fixing the first `ℓ` branches of `U`, the piece of `U^ℓ n`, the class of `ι n` for `U^{-ℓ}`);
some cell is infinite; on it both sides are single affine maps agreeing at two points, so their
slopes agree: `v₃(slope) + ℓ = v₃(slope') − ℓ`, impossible once `2ℓ` exceeds twice the largest
`|v₃|` among the finitely many piece slopes. -/
theorem no_piecewiseAffine_reversor :
    ¬ ∃ (ι : Equiv.Perm ℤ) (n : ℕ) (piece : ℤ → Fin n) (a b c : Fin n → ℤ),
      (∀ j, c j ≠ 0) ∧ (∀ x, c (piece x) * ι x = a (piece x) * x + b (piece x)) ∧
      ι * amusicalPerm * ι⁻¹ = amusicalPerm⁻¹ := by
  rintro ⟨ι, n, piece, a, b, c, hc, haff, hconj⟩
  let B : ℕ := (∑ j, (c j).natAbs) * ∑ j, (a j).natAbs
  let L : ℕ := B + 1
  have hbig : B < 3 ^ (2 * L) := by
    calc
      B < 2 ^ B := B.lt_two_pow_self
      _ ≤ 3 ^ (2 * L) := by dsimp [L]; gcongr <;> omega
  let cell : ℤ → Fin n × ZMod (4 ^ L) × Fin n × ZMod (3 ^ L) := fun x =>
    (piece x, (x : ZMod (4 ^ L)), piece (amusical^[L] x), (ι x : ZMod (3 ^ L)))
  obtain ⟨x, y, hxy, hcell⟩ := Finite.exists_ne_map_eq_of_infinite cell
  have hp₀ : piece x = piece y := by
    simpa [cell] using congrArg (fun z => z.1) hcell
  have hm₄ : (x : ZMod (4 ^ L)) = (y : ZMod (4 ^ L)) := by
    simpa [cell] using congrArg (fun z => z.2.1) hcell
  have hp₁ : piece (amusical^[L] x) = piece (amusical^[L] y) := by
    simpa [cell] using congrArg (fun z => z.2.2.1) hcell
  have hm₃ : (ι x : ZMod (3 ^ L)) = (ι y : ZMod (3 ^ L)) := by
    simpa [cell] using congrArg (fun z => z.2.2.2) hcell
  obtain ⟨k, hy⟩ := Int.modEq_iff_add_fac.mp
    ((ZMod.intCast_eq_intCast_iff x y (4 ^ L)).mp hm₄)
  have hy' : y = x + (4 : ℤ) ^ L * k := by simpa using hy
  obtain ⟨q, hιy⟩ := Int.modEq_iff_add_fac.mp
    ((ZMod.intCast_eq_intCast_iff (ι x) (ι y) (3 ^ L)).mp hm₃)
  have hιy' : ι y = ι x + (3 : ℤ) ^ L * q := by simpa using hιy
  have hk : k ≠ 0 := by
    intro hk
    apply hxy
    have : y = x := by simpa [hk] using hy'
    exact this.symm
  have hsem : SemiconjBy ι amusicalPerm amusicalPerm⁻¹ := by
    rw [SemiconjBy]
    calc
      ι * amusicalPerm = (ι * amusicalPerm * ι⁻¹) * ι := by group
      _ = amusicalPerm⁻¹ * ι := by rw [hconj]
  have hiterate : ∀ z : ℤ, ι (amusical^[L] z) = amusicalInv^[L] (ι z) := by
    intro z
    have hz := congrArg (fun p : Equiv.Perm ℤ => p z) (hsem.pow_right L).eq
    rw [amusical_iterate_eq_perm_pow, amusicalInv_iterate_eq_perm_pow]
    simpa [zpow_natCast, zpow_neg, Equiv.Perm.mul_apply] using hz
  have hforward : amusical^[L] y = amusical^[L] x +
      (3 : ℤ) ^ L * 2 ^ amusicalForwardEvenCount L x * k := by
    rw [hy']
    simpa using amusical_iterate_add_pow_four_mul_slope L L le_rfl x k
  have hbackward : amusicalInv^[L] (ι y) = amusicalInv^[L] (ι x) +
      (2 : ℤ) ^ (L + amusicalBackwardFourCount L (ι x)) * q := by
    rw [hιy']
    simpa using amusicalInv_iterate_add_pow_three_mul_slope L L le_rfl (ι x) q
  have hdiff₀ : c (piece x) * (ι y - ι x) = a (piece x) * (y - x) := by
    have hx := haff x
    have hy := haff y
    rw [← hp₀] at hy
    linear_combination hy - hx
  have ha₀ : a (piece x) ≠ 0 := by
    intro ha₀
    have hz : c (piece x) * (ι y - ι x) = 0 := by simpa [ha₀] using hdiff₀
    have hsub : ι y - ι x = 0 := (mul_eq_zero.mp hz).resolve_left (hc _)
    exact hxy ((ι.injective (sub_eq_zero.mp hsub)).symm)
  have hdiff₁ : c (piece (amusical^[L] x)) *
        (ι (amusical^[L] y) - ι (amusical^[L] x)) =
      a (piece (amusical^[L] x)) * (amusical^[L] y - amusical^[L] x) := by
    have hx := haff (amusical^[L] x)
    have hy := haff (amusical^[L] y)
    rw [← hp₁] at hy
    linear_combination hy - hx
  have heq₀ : c (piece x) * ((3 : ℤ) ^ L * q) =
      a (piece x) * ((4 : ℤ) ^ L * k) := by
    calc
      c (piece x) * ((3 : ℤ) ^ L * q) = c (piece x) * (ι y - ι x) := by rw [hιy']; ring
      _ = a (piece x) * (y - x) := hdiff₀
      _ = a (piece x) * ((4 : ℤ) ^ L * k) := by rw [hy']; ring
  have hιUdiff : ι (amusical^[L] y) - ι (amusical^[L] x) =
      (2 : ℤ) ^ (L + amusicalBackwardFourCount L (ι x)) * q := by
    rw [hiterate y, hiterate x, hbackward]
    ring
  have hUdiff : amusical^[L] y - amusical^[L] x =
      (3 : ℤ) ^ L * 2 ^ amusicalForwardEvenCount L x * k := by
    rw [hforward]
    ring
  have heq₁ : c (piece (amusical^[L] x)) *
        ((2 : ℤ) ^ (L + amusicalBackwardFourCount L (ι x)) * q) =
      a (piece (amusical^[L] x)) *
        ((3 : ℤ) ^ L * 2 ^ amusicalForwardEvenCount L x * k) := by
    calc
      _ = c (piece (amusical^[L] x)) *
          (ι (amusical^[L] y) - ι (amusical^[L] x)) := by rw [hιUdiff]
      _ = a (piece (amusical^[L] x)) * (amusical^[L] y - amusical^[L] x) := hdiff₁
      _ = _ := by rw [hUdiff]
  have hcross :
      ((c (piece (amusical^[L] x)) * a (piece x)) *
        ((4 : ℤ) ^ L * 2 ^ (L + amusicalBackwardFourCount L (ι x)))) * k =
      (((3 : ℤ) ^ L * 3 ^ L) *
        (c (piece x) * a (piece (amusical^[L] x)) *
          2 ^ amusicalForwardEvenCount L x)) * k := by
    calc
      _ = (c (piece (amusical^[L] x)) *
          2 ^ (L + amusicalBackwardFourCount L (ι x))) *
          (a (piece x) * (4 ^ L * k)) := by ring
      _ = (c (piece (amusical^[L] x)) *
          2 ^ (L + amusicalBackwardFourCount L (ι x))) *
          (c (piece x) * (3 ^ L * q)) := by rw [heq₀]
      _ = (c (piece x) * 3 ^ L) *
          (c (piece (amusical^[L] x)) *
            (2 ^ (L + amusicalBackwardFourCount L (ι x)) * q)) := by ring
      _ = (c (piece x) * 3 ^ L) *
          (a (piece (amusical^[L] x)) *
            (3 ^ L * 2 ^ amusicalForwardEvenCount L x * k)) := by rw [heq₁]
      _ = _ := by ring
  have hcoeff₀ := mul_right_cancel₀ hk hcross
  have hcoeff :
      (c (piece (amusical^[L] x)) * a (piece x)) *
          (2 : ℤ) ^ (2 * L + (L + amusicalBackwardFourCount L (ι x))) =
        (3 : ℤ) ^ (2 * L) *
          (c (piece x) * a (piece (amusical^[L] x)) *
            2 ^ amusicalForwardEvenCount L x) := by
    calc
      _ = (c (piece (amusical^[L] x)) * a (piece x)) *
          ((4 : ℤ) ^ L * 2 ^ (L + amusicalBackwardFourCount L (ι x))) := by
            rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      _ = ((3 : ℤ) ^ L * 3 ^ L) *
          (c (piece x) * a (piece (amusical^[L] x)) *
            2 ^ amusicalForwardEvenCount L x) := hcoeff₀
      _ = _ := by rw [← pow_add]; congr 2; omega
  have hdivInt : (3 : ℤ) ^ (2 * L) ∣
      (c (piece (amusical^[L] x)) * a (piece x)) *
        (2 : ℤ) ^ (2 * L + (L + amusicalBackwardFourCount L (ι x))) := by
    exact ⟨_, hcoeff⟩
  have hdivInt' : ((3 ^ (2 * L) : ℕ) : ℤ) ∣
      (c (piece (amusical^[L] x)) * a (piece x)) *
        (2 : ℤ) ^ (2 * L + (L + amusicalBackwardFourCount L (ι x))) := by
    simpa using hdivInt
  have hdivNat := Int.natCast_dvd.mp hdivInt'
  simp only [Int.natAbs_mul, Int.natAbs_pow] at hdivNat
  norm_num at hdivNat
  have hdivCoeff : 3 ^ (2 * L) ∣
      (c (piece (amusical^[L] x))).natAbs * (a (piece x)).natAbs :=
    ((Nat.Coprime.pow (2 * L)
      (2 * L + (L + amusicalBackwardFourCount L (ι x)))
      (by decide : Nat.Coprime 3 2)).dvd_mul_right).mp hdivNat
  have hcoeff_ne : (c (piece (amusical^[L] x))).natAbs * (a (piece x)).natAbs ≠ 0 :=
    mul_ne_zero (Int.natAbs_ne_zero.mpr (hc _)) (Int.natAbs_ne_zero.mpr ha₀)
  have hle : 3 ^ (2 * L) ≤
      (c (piece (amusical^[L] x))).natAbs * (a (piece x)).natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hcoeff_ne) hdivCoeff
  have hB : (c (piece (amusical^[L] x))).natAbs * (a (piece x)).natAbs ≤ B := by
    dsimp [B]
    apply Nat.mul_le_mul
    · exact Finset.single_le_sum (f := fun j ↦ (c j).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)
    · exact Finset.single_le_sum (f := fun j ↦ (a j).natAbs)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)
  omega

end CollatzMoonshot.Amusical
