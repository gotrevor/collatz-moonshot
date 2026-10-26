/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.WeakDecayTwistBound

/-!
# Sec7P with a finer character modulus

The slice has `a` odd steps, but the character in `WeakDecay.lean` has modulus
`3^(a+k)`.  This file separates those two parameters in the exact gap-pairing argument.  The
resulting Pascal damping has only `a / 2` coordinates while its pair factors live at the finer
modulus.  It is compared with the established full Sec7P damping by padding the missing pair
sums with `2`; those factors have norm one.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB
open scoped ComplexConjugate

/-! ## Exact reindexing at a finer modulus -/

/-- The positive fine-modulus character attached directly to a parity-word numerator. -/
noncomputable def fineSubsetCharTerm (n ξ : ℕ) (u : Finset ℕ) : ℂ :=
  ZMod.stdAddChar (((ξ * wordNumer u : ℕ) : ZMod (3 ^ n)))

/-- The fine-modulus character sum over the `a`-subsets of `[0,j)`. -/
noncomputable def fineSubsetChar (j a n ξ : ℕ) : ℂ :=
  ∑ u ∈ (Finset.range j).powersetCard a, fineSubsetCharTerm n ξ u

/-- Terras reindexing for the numerator character, with a modulus independent of the slice
cardinality. -/
theorem numeratorExpSum_eq_fineSubsetChar (j a n ξ : ℕ) :
    ∑ r ∈ levelSet j a,
      Complex.exp (2 * Real.pi * Complex.I *
        (((ξ * (2 ^ j * tstep^[j] r - 3 ^ a * r) : ℕ) : ℂ) / (3 ^ n : ℂ))) =
      fineSubsetChar j a n ξ := by
  unfold fineSubsetChar
  refine Finset.sum_nbij (fun r => onesSet r j) ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.mem_powerset.mp (onesSet_mem_powerset r j),
      card_onesSet r j |>.trans (Finset.mem_filter.mp hr).2⟩
  · intro r hr s hs hrs
    exact onesSet_injOn j
      (Finset.mem_coe.mpr (Finset.mem_filter.mp hr).1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mp hs).1) hrs
  · intro u hu
    have hu' := Finset.mem_coe.mp hu
    rw [Finset.mem_powersetCard] at hu'
    rcases onesSet_surjOn j
      (Finset.mem_coe.mpr (Finset.mem_powerset.mpr hu'.1)) with ⟨r, hr, hru⟩
    refine ⟨r, ?_, hru⟩
    apply Finset.mem_coe.mpr
    rw [levelSet, Finset.mem_filter]
    refine ⟨Finset.mem_coe.mp hr, ?_⟩
    change onesSet r j = u at hru
    rw [← card_onesSet r j, hru, hu'.2]
  · intro r hr
    have ha : oddCount r j = a := (Finset.mem_filter.mp hr).2
    rw [iterateNumerator_eq_numer ha, ← wordNumer_onesSet]
    unfold fineSubsetCharTerm
    exact (stdAddChar_nat_eq_exp n (ξ * wordNumer (onesSet r j))).symm

/-- The ordered-gap residue identity remains valid in any finer modulus. -/
theorem wordNumer_mul_inv_eq_sum_reverseOddTime_fine {j a n : ℕ} {u : Finset ℕ}
    (hsub : u ⊆ Finset.range j) (hu : u.card = a) :
    (wordNumer u : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ ^ j =
      ∑ m : Fin a, (3 : ZMod (3 ^ n)) ^ (m : ℕ) *
        (2 : ZMod (3 ^ n))⁻¹ ^ reverseOddTime j u hu m := by
  rw [wordNumer_eq_sum_orderEmbOfFin hu]
  push_cast
  rw [Finset.sum_mul]
  apply Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin a)) _ _
  intro m
  have hmem : u.orderEmbOfFin hu m ∈ u := u.orderEmbOfFin_mem hu _
  have hlt : u.orderEmbOfFin hu m < j := Finset.mem_range.mp (hsub hmem)
  have hrev : a - 1 - (m : ℕ) = (Fin.rev m : ℕ) := by
    simp only [Fin.rev]
    omega
  change (3 : ZMod (3 ^ n)) ^ (a - 1 - (m : ℕ)) *
      (2 : ZMod (3 ^ n)) ^ (u.orderEmbOfFin hu m) *
        (2 : ZMod (3 ^ n))⁻¹ ^ j =
    (3 : ZMod (3 ^ n)) ^ (Fin.rev m : ℕ) *
      (2 : ZMod (3 ^ n))⁻¹ ^ reverseOddTime j u hu (Fin.rev m)
  rw [hrev, mul_assoc, two_pow_mul_inv_pow hlt.le]
  simp [reverseOddTime]

/-- The negative fine-modulus character of a positive gap vector. -/
noncomputable def fineGapCharTerm (n a ξ : ℕ) (g : Fin a → ℕ) : ℂ :=
  ∏ m : Fin a, charZ n
    ((ξ : ZMod (3 ^ n)) * (3 : ZMod (3 ^ n)) ^ (m : ℕ) *
      (2 : ZMod (3 ^ n))⁻¹ ^ gapTime g m)

/-- Negative-character subset sum at the shifted frequency `ξ 2^j`. -/
noncomputable def fineNegativeSubsetChar (j a n ξ : ℕ) : ℂ :=
  ∑ u ∈ (Finset.range j).powersetCard a,
    charZ n (((ξ * 2 ^ j : ℕ) : ZMod (3 ^ n)) *
      ((wordNumer u : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ ^ j))

theorem shifted_wordNumer_cancel (j n ξ : ℕ) (u : Finset ℕ) :
    (((ξ * 2 ^ j : ℕ) : ZMod (3 ^ n)) *
        ((wordNumer u : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ ^ j)) =
      ((ξ * wordNumer u : ℕ) : ZMod (3 ^ n)) := by
  have hcop : Nat.Coprime 2 (3 ^ n) :=
    Nat.Coprime.pow_right n (by decide : Nat.Coprime 2 3)
  have hunit : (2 : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one 2 hcop
  push_cast
  calc
    (ξ : ZMod (3 ^ n)) * 2 ^ j *
        ((wordNumer u : ZMod (3 ^ n)) * 2⁻¹ ^ j) =
      (ξ : ZMod (3 ^ n)) * (wordNumer u : ZMod (3 ^ n)) *
        (2 ^ j * 2⁻¹ ^ j) := by ring
    _ = (ξ : ZMod (3 ^ n)) * (wordNumer u : ZMod (3 ^ n)) := by
      rw [← mul_pow, hunit, one_pow, mul_one]

theorem fineSubsetChar_eq_conj_fineNegativeSubsetChar (j a n ξ : ℕ) :
    fineSubsetChar j a n ξ = conj (fineNegativeSubsetChar j a n ξ) := by
  unfold fineSubsetChar fineNegativeSubsetChar fineSubsetCharTerm
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [shifted_wordNumer_cancel]
  calc
    ZMod.stdAddChar (((ξ * wordNumer u : ℕ) : ZMod (3 ^ n))) =
        (charZ n (((ξ * wordNumer u : ℕ) : ZMod (3 ^ n))))⁻¹ := by
      rw [charZ_eq_inv_stdAddChar, inv_inv]
    _ = conj (charZ n (((ξ * wordNumer u : ℕ) : ZMod (3 ^ n)))) :=
      Complex.inv_eq_conj (norm_charZ n _)

theorem norm_fineSubsetChar_eq_norm_fineNegativeSubsetChar (j a n ξ : ℕ) :
    ‖fineSubsetChar j a n ξ‖ = ‖fineNegativeSubsetChar j a n ξ‖ := by
  rw [fineSubsetChar_eq_conj_fineNegativeSubsetChar, Complex.norm_conj]

theorem charZ_fineSliceResidue_eq_fineGapCharTerm {j a n ξ : ℕ} {u : Finset ℕ}
    (hsub : u ⊆ Finset.range j) (hu : u.card = a) :
    charZ n (((ξ * 2 ^ j : ℕ) : ZMod (3 ^ n)) *
      ((wordNumer u : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ ^ j)) =
      fineGapCharTerm n a (ξ * 2 ^ j) (subsetGaps j u hu) := by
  rw [wordNumer_mul_inv_eq_sum_reverseOddTime_fine hsub hu, Finset.mul_sum]
  rw [charZ_sum n Finset.univ]
  unfold fineGapCharTerm
  apply Finset.prod_congr rfl
  intro m _
  apply congrArg (charZ n)
  rw [gapTime_subsetGaps hsub hu]
  ring

/-- Exact finite reindexing by positive gaps at the finer modulus. -/
theorem fineNegativeSubsetChar_eq_sum_gapVector (j a n ξ : ℕ) :
    fineNegativeSubsetChar j a n ξ =
      ∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a (ξ * 2 ^ j) g := by
  unfold fineNegativeSubsetChar
  calc
    ∑ u ∈ (Finset.range j).powersetCard a,
        charZ n (((ξ * 2 ^ j : ℕ) : ZMod (3 ^ n)) *
          ((wordNumer u : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ ^ j)) =
      ∑ u : ↥((Finset.range j).powersetCard a),
        charZ n (((ξ * 2 ^ j : ℕ) : ZMod (3 ^ n)) *
          ((wordNumer u.1 : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ ^ j)) := by
        exact (Finset.sum_coe_sort ((Finset.range j).powersetCard a) _).symm
    _ = ∑ g : ↥(gapVectorFinset j a), fineGapCharTerm n a (ξ * 2 ^ j) g.1 := by
      apply Fintype.sum_equiv (sliceGapEquiv j a)
      intro u
      exact charZ_fineSliceResidue_eq_fineGapCharTerm
        (Finset.mem_powersetCard.mp u.2).1 (Finset.mem_powersetCard.mp u.2).2
    _ = ∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a (ξ * 2 ^ j) g := by
      exact Finset.sum_coe_sort (gapVectorFinset j a) _

/-! ## Pair cancellation with separate slice and modulus parameters -/

noncomputable def fineGapCharFactor (n a ξ : ℕ) (g : Fin a → ℕ) (i : Fin a) : ℂ :=
  charZ n ((ξ : ZMod (3 ^ n)) * (3 : ZMod (3 ^ n)) ^ (i : ℕ) *
    (2 : ZMod (3 ^ n))⁻¹ ^ gapTime g i)

theorem fineGapCharFactor_pair {n a ξ : ℕ} (g : Fin a → ℕ) (q : Fin (a / 2)) :
    fineGapCharFactor n a ξ g (pairGapIndex a q 0) *
        fineGapCharFactor n a ξ g (pairGapIndex a q 1) =
      charZ n (xArg n ξ q (gapPairPrefix (gapPairVector g) q) *
        ((2 : ZMod (3 ^ n)) ^ g (pairGapIndex a q 1) + 3)) := by
  let s := gapPairBefore (gapPairVector g) q
  have hzero := gapTime_pair_zero g q
  have hone := gapTime_pair_one g q
  have hprefix := gapPairPrefix_eq_before_add (gapPairVector g) q
  have hprefeq : s + g (pairGapIndex a q 0) + g (pairGapIndex a q 1) =
      gapPairPrefix (gapPairVector g) q := by
    rw [hprefix]
    unfold s gapPairVector
    omega
  have htime0 : gapTime g (pairGapIndex a q 0) =
      s + g (pairGapIndex a q 0) := hzero
  have htime1 : gapTime g (pairGapIndex a q 1) =
      s + g (pairGapIndex a q 0) + g (pairGapIndex a q 1) := by
    rw [hone, ← hprefeq]
  calc
    fineGapCharFactor n a ξ g (pairGapIndex a q 0) *
        fineGapCharFactor n a ξ g (pairGapIndex a q 1) =
      charZ n (xArg n ξ q
        (s + g (pairGapIndex a q 0) + g (pairGapIndex a q 1)) *
          ((2 : ZMod (3 ^ n)) ^ g (pairGapIndex a q 1) + 3)) := by
        simpa only [fineGapCharFactor, pairGapIndex_val, Fin.val_zero, Fin.val_one,
          Nat.add_zero, htime0, htime1] using
          charZ_two_gap_terms n ξ q s
            (g (pairGapIndex a q 0)) (g (pairGapIndex a q 1))
    _ = charZ n (xArg n ξ q (gapPairPrefix (gapPairVector g) q) *
        ((2 : ZMod (3 ^ n)) ^ g (pairGapIndex a q 1) + 3)) := by rw [hprefeq]

noncomputable def fineGapTailCharProduct (n a ξ : ℕ) (b : Fin (a / 2) → ℕ)
    (t : Fin (a % 2) → ℕ) : ℂ :=
  ∏ r : Fin (a % 2), charZ n
    ((ξ : ZMod (3 ^ n)) * (3 : ZMod (3 ^ n)) ^ (tailGapIndex a r : ℕ) *
      (2 : ZMod (3 ^ n))⁻¹ ^ ((∑ q, b q) + t r))

theorem norm_fineGapTailCharProduct (n a ξ : ℕ) (b : Fin (a / 2) → ℕ)
    (t : Fin (a % 2) → ℕ) : ‖fineGapTailCharProduct n a ξ b t‖ = 1 := by
  unfold fineGapTailCharProduct
  rw [Complex.norm_prod]
  simp only [norm_charZ, Finset.prod_const_one]

theorem fineGapCharTerm_eq_pair_prod_mul_tail (n a ξ : ℕ) (g : Fin a → ℕ) :
    fineGapCharTerm n a ξ g =
      (∏ q : Fin (a / 2),
        charZ n (xArg n ξ q (gapPairPrefix (gapPairVector g) q) *
          ((2 : ZMod (3 ^ n)) ^ g (pairGapIndex a q 1) + 3))) *
        fineGapTailCharProduct n a ξ (gapPairVector g) (gapTailVector g) := by
  unfold fineGapCharTerm
  change (∏ i : Fin a, fineGapCharFactor n a ξ g i) = _
  rw [← (gapBlockEquiv a).prod_comp (fineGapCharFactor n a ξ g),
    Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two]
  congr 1
  · apply Finset.prod_congr rfl
    intro q _
    exact fineGapCharFactor_pair g q
  · unfold fineGapTailCharProduct fineGapCharFactor
    apply Finset.prod_congr rfl
    intro r _
    change charZ n ((ξ : ZMod (3 ^ n)) *
      (3 : ZMod (3 ^ n)) ^ (tailGapIndex a r : ℕ) *
        (2 : ZMod (3 ^ n))⁻¹ ^ gapTime g (tailGapIndex a r)) = _
    rw [gapTime_tail]

theorem fineGapCharTerm_splitGapVectorNat {n a ξ : ℕ} {b d : Fin (a / 2) → ℕ}
    (hd : ∀ q, d q ∈ Finset.Icc 1 (b q - 1)) (t : Fin (a % 2) → ℕ) :
    fineGapCharTerm n a ξ (splitGapVectorNat b d t) =
      (∏ q : Fin (a / 2),
        charZ n (xArg n ξ q (gapPairPrefix b q) *
          ((2 : ZMod (3 ^ n)) ^ d q + 3))) * fineGapTailCharProduct n a ξ b t := by
  rw [fineGapCharTerm_eq_pair_prod_mul_tail,
    gapPairVector_splitGapVectorNat hd t, gapTailVector_splitGapVectorNat]
  apply congrArg₂ (· * ·) ?_ rfl
  apply Finset.prod_congr rfl
  intro q _
  rw [splitGapVectorNat_pair_one]

/-- The gap-fiber reindexing is purely combinatorial, so it applies to any summand. -/
theorem sum_gapFiberFinset_eq_splits_apply {R : Type*} [AddCommMonoid R]
    {j a : ℕ} {b : Fin (a / 2) → ℕ} {t : Fin (a % 2) → ℕ}
    (ht : ∀ r, 0 < t r) (htotal : (∑ q, b q) + ∑ r, t r ≤ j)
    (F : (Fin a → ℕ) → R) :
    ∑ g ∈ gapFiberFinset j a b t, F g =
      ∑ d ∈ splitChoiceFinset b, F (splitGapVectorNat b d t) := by
  classical
  symm
  apply Finset.sum_bij (fun d _ => splitGapVectorNat b d t)
  · intro d hd
    have hd' := mem_splitChoiceFinset.mp hd
    rw [mem_gapFiberFinset]
    refine ⟨mem_gapVectorFinset.mpr ⟨splitGapVectorNat_pos hd' ht, ?_⟩, ?_, ?_⟩
    · rw [sum_splitGapVectorNat hd' t]
      exact htotal
    · exact gapPairVector_splitGapVectorNat hd' t
    · exact gapTailVector_splitGapVectorNat b d t
  · intro d₁ hd₁ d₂ hd₂ heq
    funext q
    have h := congr_fun heq (pairGapIndex a q 1)
    simpa using h
  · intro g hg
    have hgf := mem_gapFiberFinset.mp hg
    let d : Fin (a / 2) → ℕ := fun q => g (pairGapIndex a q 1)
    have hgpos := (mem_gapVectorFinset.mp hgf.1).1
    have hd : d ∈ splitChoiceFinset b := by
      rw [mem_splitChoiceFinset]
      intro q
      rw [Finset.mem_Icc]
      change 1 ≤ g (pairGapIndex a q 1) ∧ g (pairGapIndex a q 1) ≤ b q - 1
      have hpair := congr_fun hgf.2.1 q
      unfold gapPairVector at hpair
      constructor
      · exact hgpos (pairGapIndex a q 1)
      · have hzero := hgpos (pairGapIndex a q 0)
        omega
    refine ⟨d, hd, ?_⟩
    rw [← hgf.2.1, ← hgf.2.2]
    exact splitGapVectorNat_of_gap g
  · intro d hd
    rfl

theorem sum_fineGapFiberFinset {j n a ξ : ℕ} {b : Fin (a / 2) → ℕ}
    (hb : ∀ q, 2 ≤ b q) {t : Fin (a % 2) → ℕ} (ht : ∀ r, 0 < t r)
    (htotal : (∑ q, b q) + ∑ r, t r ≤ j) :
    ∑ g ∈ gapFiberFinset j a b t, fineGapCharTerm n a ξ g =
      (∏ q : Fin (a / 2),
        ((b q : ℂ) - 1) * fPair n (xArg n ξ q (gapPairPrefix b q)) (b q)) *
        fineGapTailCharProduct n a ξ b t := by
  classical
  rw [sum_gapFiberFinset_eq_splits_apply ht htotal]
  calc
    ∑ d ∈ splitChoiceFinset b, fineGapCharTerm n a ξ (splitGapVectorNat b d t) =
        ∑ d ∈ splitChoiceFinset b,
          (∏ q : Fin (a / 2),
            charZ n (xArg n ξ q (gapPairPrefix b q) *
              ((2 : ZMod (3 ^ n)) ^ d q + 3))) * fineGapTailCharProduct n a ξ b t := by
      apply Finset.sum_congr rfl
      intro d hd
      exact fineGapCharTerm_splitGapVectorNat (mem_splitChoiceFinset.mp hd) t
    _ = (∑ d ∈ splitChoiceFinset b,
          ∏ q : Fin (a / 2),
            charZ n (xArg n ξ q (gapPairPrefix b q) *
              ((2 : ZMod (3 ^ n)) ^ d q + 3))) * fineGapTailCharProduct n a ξ b t := by
      rw [Finset.sum_mul]
    _ = (∏ q : Fin (a / 2), ∑ d ∈ Finset.Icc 1 (b q - 1),
          charZ n (xArg n ξ q (gapPairPrefix b q) *
            ((2 : ZMod (3 ^ n)) ^ d + 3))) * fineGapTailCharProduct n a ξ b t := by
      rw [Finset.prod_univ_sum]
      rfl
    _ = (∏ q : Fin (a / 2),
          ((b q : ℂ) - 1) * fPair n (xArg n ξ q (gapPairPrefix b q)) (b q)) *
          fineGapTailCharProduct n a ξ b t := by
      congr 1
      apply Finset.prod_congr rfl
      intro q _
      exact sum_charZ_splits_eq_mul_fPair n _ (hb q)

theorem norm_sum_fineGapFiberFinset {j n a ξ : ℕ} {b : Fin (a / 2) → ℕ}
    (hb : ∀ q, 2 ≤ b q) {t : Fin (a % 2) → ℕ} (ht : ∀ r, 0 < t r)
    (htotal : (∑ q, b q) + ∑ r, t r ≤ j) :
    ‖∑ g ∈ gapFiberFinset j a b t, fineGapCharTerm n a ξ g‖ =
      ∏ q : Fin (a / 2),
        ((b q : ℝ) - 1) * ‖fPair n (xArg n ξ q (gapPairPrefix b q)) (b q)‖ := by
  rw [sum_fineGapFiberFinset hb ht htotal, norm_mul, norm_fineGapTailCharProduct, mul_one,
    Complex.norm_prod]
  apply Finset.prod_congr rfl
  intro q _
  rw [norm_mul]
  congr 1
  rw [Complex.norm_def, Complex.normSq_apply]
  simp
  have hb1 : (1 : ℝ) ≤ b q := by exact_mod_cast (hb q).trans' (by omega)
  rw [← sq, Real.sqrt_sq (sub_nonneg.mpr hb1)]

theorem sum_gapVectorFinset_eq_sum_fineGapFibers (j n a ξ : ℕ) :
    ∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a ξ g =
      ∑ bt ∈ gapKeyFinset j a,
        ∑ g ∈ gapFiberFinset j a bt.1 bt.2, fineGapCharTerm n a ξ g := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := gapVectorFinset j a) (t := gapKeyFinset j a) (g := gapKey)
    (fun g hg => Finset.mem_image.mpr ⟨g, hg, rfl⟩) (fineGapCharTerm n a ξ)]
  apply Finset.sum_congr rfl
  intro bt hbt
  apply Finset.sum_congr
  · rcases bt with ⟨b, t⟩
    ext g
    simp [gapFiberFinset, gapKey]
  · intro g hg
    rfl

theorem norm_sum_fineGapVectorFinset_le_pairFibers (j n a ξ : ℕ) :
    ‖∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a ξ g‖ ≤
      ∑ bt ∈ gapKeyFinset j a, ∏ q : Fin (a / 2),
        ((bt.1 q : ℝ) - 1) *
          ‖fPair n (xArg n ξ q (gapPairPrefix bt.1 q)) (bt.1 q)‖ := by
  rw [sum_gapVectorFinset_eq_sum_fineGapFibers]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro bt hbt
  obtain ⟨hb, ht, htotal⟩ := gapKeyFinset_admissible hbt
  exact le_of_eq (norm_sum_fineGapFiberFinset hb ht htotal)

/-! ## The partial Pascal damping -/

/-- Sec7P damping with `a / 2` random pair sums but character arithmetic modulo `3^n`. -/
noncomputable def finePascalDamping (n a : ℕ) (p : ℝ) (ξ : ℕ) : ℝ :=
  ∑' b : Fin (a / 2) → ℕ, (∏ q, pascalWeight p (b q)) *
    ∏ q : Fin (a / 2),
      ‖fPair n (xArg n ξ q (gapPairPrefix b q)) (b q)‖

noncomputable def finePascalDampingTerm (n a : ℕ) (p : ℝ) (ξ : ℕ)
    (b : Fin (a / 2) → ℕ) : ℝ :=
  (∏ q, pascalWeight p (b q)) *
    ∏ q : Fin (a / 2),
      ‖fPair n (xArg n ξ q (gapPairPrefix b q)) (b q)‖

theorem finePascalDamping_eq_tsum (n a : ℕ) (p : ℝ) (ξ : ℕ) :
    finePascalDamping n a p ξ = ∑' b, finePascalDampingTerm n a p ξ b := by
  rfl

theorem finePascalDampingTerm_nonneg {p : ℝ} (hp1 : p ≤ 1) (n a ξ : ℕ)
    (b : Fin (a / 2) → ℕ) : 0 ≤ finePascalDampingTerm n a p ξ b := by
  unfold finePascalDampingTerm
  exact mul_nonneg (Finset.prod_nonneg fun q _ => pascalWeight_nonneg hp1 (b q))
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)

theorem summable_finePascalDampingTerm {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (n a ξ : ℕ) : Summable (finePascalDampingTerm n a p ξ) := by
  have hweights : Summable (fun b : Fin (a / 2) → ℕ =>
      ∏ q, pascalWeight p (b q)) :=
    summable_fin_product_of_nonneg (fun m => pascalWeight_nonneg hp1.le m)
      (summable_pascalWeight hp0 hp1) _
  refine Summable.of_nonneg_of_le
    (fun b => finePascalDampingTerm_nonneg hp1.le n a ξ b) ?_ hweights
  intro b
  unfold finePascalDampingTerm
  refine mul_le_of_le_one_right
    (Finset.prod_nonneg fun q _ => pascalWeight_nonneg hp1.le (b q)) ?_
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun q _ => norm_fPair_le_one n _ (b q))

theorem sum_finePascalDampingTerm_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (n a ξ : ℕ) (s : Finset (Fin (a / 2) → ℕ)) :
    ∑ b ∈ s, finePascalDampingTerm n a p ξ b ≤ finePascalDamping n a p ξ := by
  rw [finePascalDamping_eq_tsum]
  exact (summable_finePascalDampingTerm hp0 hp1 n a ξ).sum_le_tsum s
    (fun b _ => finePascalDampingTerm_nonneg hp1.le n a ξ b)

noncomputable def finePairFiberNorm (n a ξ : ℕ) (b : Fin (a / 2) → ℕ) : ℝ :=
  ∏ q : Fin (a / 2),
    ((b q : ℝ) - 1) *
      ‖fPair n (xArg n ξ q (gapPairPrefix b q)) (b q)‖

theorem finePairFiberNorm_nonneg {n a ξ : ℕ} {b : Fin (a / 2) → ℕ}
    (hb : ∀ q, 2 ≤ b q) : 0 ≤ finePairFiberNorm n a ξ b := by
  unfold finePairFiberNorm
  apply Finset.prod_nonneg
  intro q _
  have hbqNat : 1 ≤ b q := Nat.le_trans (by norm_num) (hb q)
  have hbq : (1 : ℝ) ≤ b q := by exact_mod_cast hbqNat
  exact mul_nonneg (sub_nonneg.mpr hbq) (norm_nonneg _)

theorem finePascalDampingTerm_eq_geom_mul_finePairFiberNorm {n a ξ : ℕ} (p : ℝ)
    {b : Fin (a / 2) → ℕ} (hb : ∀ q, 2 ≤ b q) :
    finePascalDampingTerm n a p ξ b =
      p ^ (2 * (a / 2)) * (1 - p) ^ ((∑ q, b q) - 2 * (a / 2)) *
        finePairFiberNorm n a ξ b := by
  have hweight : (∏ q, pascalWeight p (b q)) =
      (∏ q, ((b q : ℝ) - 1)) * p ^ (2 * (a / 2)) *
        (1 - p) ^ ((∑ q, b q) - 2 * (a / 2)) := by
    simp_rw [pascalWeight_of_two_le p (hb _)]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul, Finset.prod_pow_eq_pow_sum, sum_pair_sub_two hb]
  unfold finePascalDampingTerm finePairFiberNorm
  rw [hweight, Finset.prod_mul_distrib]
  ring

theorem weighted_finePairFiberNorm_le_finePascalDampingTerm {j n a ξ : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    {bt : (Fin (a / 2) → ℕ) × (Fin (a % 2) → ℕ)}
    (hbt : bt ∈ gapKeyFinset j a) :
    p ^ a * (1 - p) ^ (j - a) * finePairFiberNorm n a ξ bt.1 ≤
      finePascalDampingTerm n a p ξ bt.1 := by
  obtain ⟨hb, ht, htotal⟩ := gapKeyFinset_admissible hbt
  let qn := a / 2
  let r := a % 2
  let S := ∑ q, bt.1 q
  have hrlt : r < 2 := by
    unfold r
    exact Nat.mod_lt _ (by omega)
  have ha : a = 2 * qn + r := by
    unfold qn r
    have h := Nat.div_add_mod a 2
    omega
  have htwo : 2 * qn ≤ S := by
    unfold qn S
    calc
      2 * (a / 2) = ∑ q : Fin (a / 2), 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ q, bt.1 q := Finset.sum_le_sum fun q _ => hb q
  have hrtail : r ≤ ∑ t, bt.2 t := by
    by_cases hr0 : r = 0
    · simp [hr0]
    · have hr1 : r = 1 := by omega
      let t0 : Fin (a % 2) := ⟨0, by simp [r, hr1]⟩
      have hsingle : bt.2 t0 ≤ ∑ t, bt.2 t :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t0)
      have ht0 := ht t0
      omega
  have hSj : S + r ≤ j := by
    change S + ∑ t, bt.2 t ≤ j at htotal
    omega
  have hpPow : p ^ a = p ^ (2 * qn) * p ^ r := by rw [ha, pow_add]
  have hqPow : (1 - p) ^ (j - a) =
      (1 - p) ^ (S - 2 * qn) * (1 - p) ^ (j - S - r) := by
    rw [← pow_add]
    congr 1
    omega
  have hid : p ^ a * (1 - p) ^ (j - a) * finePairFiberNorm n a ξ bt.1 =
      (p ^ (2 * qn) * (1 - p) ^ (S - 2 * qn) * finePairFiberNorm n a ξ bt.1) *
        (p ^ r * (1 - p) ^ (j - S - r)) := by
    rw [hpPow, hqPow]
    ring
  have hq0 : 0 ≤ 1 - p := by linarith
  have hfactor : p ^ r * (1 - p) ^ (j - S - r) ≤ 1 := by
    calc
      p ^ r * (1 - p) ^ (j - S - r) ≤ 1 * 1 :=
        mul_le_mul (pow_le_one₀ hp0.le hp1.le) (pow_le_one₀ hq0 (by linarith))
          (pow_nonneg hq0 _) zero_le_one
      _ = 1 := one_mul 1
  rw [finePascalDampingTerm_eq_geom_mul_finePairFiberNorm p hb]
  change _ ≤ p ^ (2 * qn) * (1 - p) ^ (S - 2 * qn) * finePairFiberNorm n a ξ bt.1
  rw [hid]
  calc
    (p ^ (2 * qn) * (1 - p) ^ (S - 2 * qn) * finePairFiberNorm n a ξ bt.1) *
          (p ^ r * (1 - p) ^ (j - S - r)) ≤
        (p ^ (2 * qn) * (1 - p) ^ (S - 2 * qn) * finePairFiberNorm n a ξ bt.1) * 1 :=
      mul_le_mul_of_nonneg_left hfactor
        (mul_nonneg (mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg hq0 _))
          (finePairFiberNorm_nonneg hb))
    _ = p ^ (2 * qn) * (1 - p) ^ (S - 2 * qn) * finePairFiberNorm n a ξ bt.1 := by
      ring

theorem sum_gapKey_finePascalDampingTerm_le {j n a ξ : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∑ bt ∈ gapKeyFinset j a, finePascalDampingTerm n a p ξ bt.1 ≤
      (j + 1 : ℝ) * finePascalDamping n a p ξ := by
  let bs := pairKeyFinset j a
  let ts := tailChoiceFinset j a
  have hsubset : gapKeyFinset j a ⊆ bs.product ts := by
    exact gapKeyFinset_subset_pair_product j a
  have hfinite := sum_finePascalDampingTerm_le hp0 hp1 n a ξ bs
  have hcard : (ts.card : ℝ) ≤ j + 1 := by
    exact_mod_cast card_tailChoiceFinset_le j a
  have hsum0 : 0 ≤ ∑ b ∈ bs, finePascalDampingTerm n a p ξ b :=
    Finset.sum_nonneg fun b _ => finePascalDampingTerm_nonneg hp1.le n a ξ b
  calc
    ∑ bt ∈ gapKeyFinset j a, finePascalDampingTerm n a p ξ bt.1 ≤
        ∑ bt ∈ bs.product ts, finePascalDampingTerm n a p ξ bt.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun bt _ _ => finePascalDampingTerm_nonneg hp1.le n a ξ bt.1)
    _ = (ts.card : ℝ) * ∑ b ∈ bs, finePascalDampingTerm n a p ξ b := by
      rw [Finset.product_eq_sprod, Finset.sum_product]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.mul_sum]
    _ ≤ (j + 1 : ℝ) * ∑ b ∈ bs, finePascalDampingTerm n a p ξ b :=
      mul_le_mul_of_nonneg_right hcard hsum0
    _ ≤ (j + 1 : ℝ) * finePascalDamping n a p ξ :=
      mul_le_mul_of_nonneg_left hfinite (by positivity)

theorem weighted_fineGapCharSum_le_finePascalDamping {j n a ξ : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    p ^ a * (1 - p) ^ (j - a) *
        ‖∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a ξ g‖ ≤
      (j + 1 : ℝ) * finePascalDamping n a p ξ := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hweight : 0 ≤ p ^ a * (1 - p) ^ (j - a) :=
    mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg hq0 _)
  have hnorm :
      ‖∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a ξ g‖ ≤
        ∑ bt ∈ gapKeyFinset j a, finePairFiberNorm n a ξ bt.1 := by
    simpa only [finePairFiberNorm] using norm_sum_fineGapVectorFinset_le_pairFibers j n a ξ
  calc
    p ^ a * (1 - p) ^ (j - a) *
        ‖∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a ξ g‖ ≤
      (p ^ a * (1 - p) ^ (j - a)) *
        ∑ bt ∈ gapKeyFinset j a, finePairFiberNorm n a ξ bt.1 :=
      mul_le_mul_of_nonneg_left hnorm hweight
    _ = ∑ bt ∈ gapKeyFinset j a,
        p ^ a * (1 - p) ^ (j - a) * finePairFiberNorm n a ξ bt.1 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ bt ∈ gapKeyFinset j a, finePascalDampingTerm n a p ξ bt.1 := by
      apply Finset.sum_le_sum
      intro bt hbt
      exact weighted_finePairFiberNorm_le_finePascalDampingTerm hp0 hp1 hbt
    _ ≤ (j + 1 : ℝ) * finePascalDamping n a p ξ :=
      sum_gapKey_finePascalDampingTerm_le hp0 hp1

theorem norm_numeratorExpSum_eq_norm_fineGapCharSum (j a n ξ : ℕ) :
    ‖∑ r ∈ levelSet j a,
      Complex.exp (2 * Real.pi * Complex.I *
        (((ξ * (2 ^ j * tstep^[j] r - 3 ^ a * r) : ℕ) : ℂ) / (3 ^ n : ℂ)))‖ =
      ‖∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a (ξ * 2 ^ j) g‖ := by
  rw [numeratorExpSum_eq_fineSubsetChar,
    norm_fineSubsetChar_eq_norm_fineNegativeSubsetChar,
    fineNegativeSubsetChar_eq_sum_gapVector]

theorem norm_numeratorExpSum_le_mode_fineDamping {j a n ξ : ℕ}
    (hj : 0 < j) (ha0 : 0 < a) (ha : a < j) :
    ‖∑ r ∈ levelSet j a,
      Complex.exp (2 * Real.pi * Complex.I *
        (((ξ * (2 ^ j * tstep^[j] r - 3 ^ a * r) : ℕ) : ℂ) / (3 ^ n : ℂ)))‖ ≤
      (j + 1 : ℝ) ^ 2 * (j.choose a : ℝ) *
        finePascalDamping n a ((a : ℝ) / j) (ξ * 2 ^ j) := by
  let p : ℝ := (a : ℝ) / j
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  have hp0 : 0 < p := by unfold p; exact div_pos haR hjR
  have hp1 : p < 1 := by unfold p; exact (div_lt_one hjR).mpr (by exact_mod_cast ha)
  rw [norm_numeratorExpSum_eq_norm_fineGapCharSum]
  have hweighted := weighted_fineGapCharSum_le_finePascalDamping
    (j := j) (n := n) (a := a) (ξ := ξ * 2 ^ j) hp0 hp1
  have hchoose : (0 : ℝ) ≤ j.choose a := by positivity
  have hweighted' :
      binomialSliceWeight j a p *
          ‖∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a (ξ * 2 ^ j) g‖ ≤
        (j.choose a : ℝ) * ((j + 1 : ℝ) * finePascalDamping n a p (ξ * 2 ^ j)) := by
    have hm := mul_le_mul_of_nonneg_left hweighted hchoose
    unfold binomialSliceWeight
    calc
      (j.choose a : ℝ) * p ^ a * (1 - p) ^ (j - a) *
          ‖∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a (ξ * 2 ^ j) g‖ =
        (j.choose a : ℝ) *
          (p ^ a * (1 - p) ^ (j - a) *
            ‖∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a (ξ * 2 ^ j) g‖) := by
          ring
      _ ≤ (j.choose a : ℝ) *
          ((j + 1 : ℝ) * finePascalDamping n a p (ξ * 2 ^ j)) := hm
  have hmode : 1 / (j + 1 : ℝ) ≤ binomialSliceWeight j a p :=
    one_div_succ_le_binomialSliceWeight_mode hj ha0 ha
  have hconditioned :
      (1 / (j + 1 : ℝ)) *
          ‖∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a (ξ * 2 ^ j) g‖ ≤
        (j.choose a : ℝ) * ((j + 1 : ℝ) * finePascalDamping n a p (ξ * 2 ^ j)) :=
    (mul_le_mul_of_nonneg_right hmode (norm_nonneg _)).trans hweighted'
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  calc
    ‖∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a (ξ * 2 ^ j) g‖ =
        (j + 1 : ℝ) * ((1 / (j + 1 : ℝ)) *
          ‖∑ g ∈ gapVectorFinset j a, fineGapCharTerm n a (ξ * 2 ^ j) g‖) := by
      field_simp
    _ ≤ (j + 1 : ℝ) *
        ((j.choose a : ℝ) * ((j + 1 : ℝ) * finePascalDamping n a p (ξ * 2 ^ j))) :=
      mul_le_mul_of_nonneg_left hconditioned hj1.le
    _ = (j + 1 : ℝ) ^ 2 * (j.choose a : ℝ) *
        finePascalDamping n a p (ξ * 2 ^ j) := by ring

/-! ## Padding the partial damping into the established Sec7P damping -/

/-- A prefix sum independent of the name used for the ambient `Fin` cardinality. -/
def finPrefix {q : ℕ} (b : Fin q → ℕ) (i : Fin q) : ℕ :=
  ∑ r ∈ Finset.univ.filter (fun r : Fin q => r ≤ i), b r

theorem finPrefix_eq_gapPairPrefix {a : ℕ} (b : Fin (a / 2) → ℕ)
    (q : Fin (a / 2)) : finPrefix b q = gapPairPrefix b q := by
  rfl

/-- Append `d` pair sums equal to two, transporting across a cardinality equality. -/
def padPairSums {q d N : ℕ} (h : q + d = N) (b : Fin q → ℕ) : Fin N → ℕ :=
  fun i => Fin.append b (fun _ : Fin d => 2) (Fin.cast h.symm i)

def padPairHead {q d N : ℕ} (h : q + d = N) (i : Fin q) : Fin N :=
  Fin.cast h (Fin.castAdd d i)

def padPairTail {q d N : ℕ} (h : q + d = N) (i : Fin d) : Fin N :=
  Fin.cast h (Fin.natAdd q i)

@[simp] theorem padPairSums_head {q d N : ℕ} (h : q + d = N)
    (b : Fin q → ℕ) (i : Fin q) :
    padPairSums h b (padPairHead h i) = b i := by
  simp [padPairSums, padPairHead, Fin.append_left]

@[simp] theorem padPairSums_tail {q d N : ℕ} (h : q + d = N)
    (b : Fin q → ℕ) (i : Fin d) :
    padPairSums h b (padPairTail h i) = 2 := by
  simp [padPairSums, padPairTail, Fin.append_right]

theorem padPairSums_injective {q d N : ℕ} (h : q + d = N) :
    Function.Injective (padPairSums h : (Fin q → ℕ) → (Fin N → ℕ)) := by
  intro b c hbc
  funext i
  have hi := congr_fun hbc (padPairHead h i)
  simpa using hi

@[simp] theorem padPairHead_val {q d N : ℕ} (h : q + d = N) (i : Fin q) :
    (padPairHead h i : ℕ) = i := by
  rfl

theorem finPrefix_padPairSums_head {q d N : ℕ} (h : q + d = N)
    (b : Fin q → ℕ) (i : Fin q) :
    finPrefix (padPairSums h b) (padPairHead h i) = finPrefix b i := by
  unfold finPrefix
  rw [TaoCollatz.Sec7P.prefix_filter_eq_pre,
    TaoCollatz.Sec7P.prefix_filter_eq_pre]
  unfold TaoCollatz.pre
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m < (i : ℕ) + 1 := Finset.mem_range.mp hm
  have hmq : m < q := by omega
  have hmN : m < N := by
    have hqN : q ≤ N := by omega
    omega
  rw [dif_pos hmN, dif_pos hmq]
  have heq : (⟨m, hmN⟩ : Fin N) = padPairHead h ⟨m, hmq⟩ := by
    apply Fin.ext
    rfl
  rw [heq, padPairSums_head]

theorem norm_fPair_two (n : ℕ) (x : ZMod (3 ^ n)) : ‖fPair n x 2‖ = 1 := by
  unfold fPair
  simp [norm_charZ]
  norm_num

/-- A padded partial summand is a full Sec7P summand, times the probability `p^(2d)` of the
fixed padding coordinates. -/
theorem pascalDampingTerm_padPairSums {n a d ξ : ℕ} {p : ℝ}
    (h : a / 2 + d = n / 2) (b : Fin (a / 2) → ℕ) :
    pascalDampingTerm n p ξ (padPairSums h b) =
      finePascalDampingTerm n a p ξ b * (p ^ 2) ^ d := by
  let e : Fin (a / 2 + d) ≃ Fin (n / 2) := finCongr h
  have hpad (i : Fin (a / 2 + d)) :
      padPairSums h b (e i) = Fin.append b (fun _ : Fin d => 2) i := by
    simp [padPairSums, e]
  have hweight :
      (∏ q : Fin (n / 2), pascalWeight p (padPairSums h b q)) =
        (∏ q : Fin (a / 2), pascalWeight p (b q)) * (p ^ 2) ^ d := by
    calc
      (∏ q : Fin (n / 2), pascalWeight p (padPairSums h b q)) =
          ∏ i : Fin (a / 2 + d), pascalWeight p (padPairSums h b (e i)) := by
            exact (e.prod_comp _).symm
      _ = (∏ q : Fin (a / 2), pascalWeight p (b q)) *
          ∏ r : Fin d, pascalWeight p 2 := by
        rw [Fin.prod_univ_add]
        congr 1
        · apply Finset.prod_congr rfl
          intro q _
          rw [hpad, Fin.append_left]
        · apply Finset.prod_congr rfl
          intro r _
          rw [hpad, Fin.append_right]
      _ = (∏ q : Fin (a / 2), pascalWeight p (b q)) * (p ^ 2) ^ d := by
        congr 1
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        congr 1
        rw [pascalWeight_of_two_le p (by omega)]
        norm_num
  have hfactor :
      (∏ q : Fin (n / 2),
        ‖fPair n (xArg n ξ q (gapPairPrefix (padPairSums h b) q))
          (padPairSums h b q)‖) =
        ∏ q : Fin (a / 2), ‖fPair n (xArg n ξ q (gapPairPrefix b q)) (b q)‖ := by
    calc
      (∏ q : Fin (n / 2),
          ‖fPair n (xArg n ξ q (gapPairPrefix (padPairSums h b) q))
            (padPairSums h b q)‖) =
        ∏ i : Fin (a / 2 + d),
          ‖fPair n (xArg n ξ (e i) (gapPairPrefix (padPairSums h b) (e i)))
            (padPairSums h b (e i))‖ := by
              exact (e.prod_comp _).symm
      _ = (∏ q : Fin (a / 2),
            ‖fPair n (xArg n ξ q (gapPairPrefix b q)) (b q)‖) * 1 := by
        rw [Fin.prod_univ_add]
        congr 1
        · apply Finset.prod_congr rfl
          intro q _
          have he : e (Fin.castAdd d q) = padPairHead h q := by rfl
          rw [he, padPairSums_head]
          rw [← finPrefix_eq_gapPairPrefix b q,
            ← finPrefix_eq_gapPairPrefix (padPairSums h b) (padPairHead h q),
            finPrefix_padPairSums_head]
          rfl
        · rw [show (∏ r : Fin d,
              ‖fPair n
                (xArg n ξ (e (Fin.natAdd (a / 2) r))
                  (gapPairPrefix (padPairSums h b) (e (Fin.natAdd (a / 2) r))))
                (padPairSums h b (e (Fin.natAdd (a / 2) r)))‖) = 1 by
            apply Finset.prod_eq_one
            intro r _
            have he : e (Fin.natAdd (a / 2) r) = padPairTail h r := by rfl
            rw [he, padPairSums_tail, norm_fPair_two]]
      _ = ∏ q : Fin (a / 2),
            ‖fPair n (xArg n ξ q (gapPairPrefix b q)) (b q)‖ := by rw [mul_one]
  unfold pascalDampingTerm finePascalDampingTerm
  rw [hweight, hfactor]
  ring

theorem finePascalDamping_nonneg {n a ξ : ℕ} {p : ℝ} (hp1 : p ≤ 1) :
    0 ≤ finePascalDamping n a p ξ := by
  rw [finePascalDamping_eq_tsum]
  exact tsum_nonneg fun b => finePascalDampingTerm_nonneg hp1 n a ξ b

theorem pascalDamping_nonneg' {n ξ : ℕ} {p : ℝ} (hp1 : p ≤ 1) :
    0 ≤ pascalDamping n p ξ := by
  rw [pascalDamping_eq_tsum]
  exact tsum_nonneg fun b => pascalDampingTerm_nonneg hp1 n ξ b

/-- The mass of the fixed all-two padding embeds the partial damping in the full damping. -/
theorem pow_mul_finePascalDamping_le_pascalDamping {n a d ξ : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (h : a / 2 + d = n / 2) :
    (p ^ 2) ^ d * finePascalDamping n a p ξ ≤ pascalDamping n p ξ := by
  let f : (Fin (a / 2) → ℕ) → ℝ :=
    fun b => (p ^ 2) ^ d * finePascalDampingTerm n a p ξ b
  let g : (Fin (n / 2) → ℕ) → ℝ := pascalDampingTerm n p ξ
  have hf : Summable f :=
    (summable_finePascalDampingTerm hp0 hp1 n a ξ).mul_left ((p ^ 2) ^ d)
  have hg : Summable g := summable_pascalDampingTerm hp0 hp1 n ξ
  have hle : (∑' b, f b) ≤ ∑' c, g c :=
    hf.tsum_le_tsum_of_inj (padPairSums h) (padPairSums_injective h)
      (fun c hc => pascalDampingTerm_nonneg hp1.le n ξ c)
      (fun b => by
        dsimp [f, g]
        rw [pascalDampingTerm_padPairSums h]
        exact le_of_eq (mul_comm _ _)) hg
  calc
    (p ^ 2) ^ d * finePascalDamping n a p ξ = ∑' b, f b := by
      rw [finePascalDamping_eq_tsum, tsum_mul_left]
    _ ≤ ∑' c, g c := hle
    _ = pascalDamping n p ξ := by rfl

/-- Uniformly for `p ≥ 1/5`, padding `d` pair sums costs at most `25^d`. -/
theorem finePascalDamping_le_pow_mul_pascalDamping {n a d ξ : ℕ} {p : ℝ}
    (hp0 : 1 / 5 ≤ p) (hp1 : p < 1) (h : a / 2 + d = n / 2) :
    finePascalDamping n a p ξ ≤ (25 : ℝ) ^ d * pascalDamping n p ξ := by
  have hp0' : 0 < p := by linarith
  have hpad := pow_mul_finePascalDamping_le_pascalDamping (ξ := ξ) hp0' hp1 h
  have hbase : (1 / 25 : ℝ) ≤ p ^ 2 := by
    nlinarith [sq_nonneg (p - 1 / 5)]
  have hpow : (1 / 25 : ℝ) ^ d ≤ (p ^ 2) ^ d :=
    pow_le_pow_left₀ (by norm_num) hbase d
  have hfine0 : 0 ≤ finePascalDamping n a p ξ :=
    finePascalDamping_nonneg (by linarith)
  have hsmall : (1 / 25 : ℝ) ^ d * finePascalDamping n a p ξ ≤
      pascalDamping n p ξ :=
    (mul_le_mul_of_nonneg_right hpow hfine0).trans hpad
  calc
    finePascalDamping n a p ξ =
        (25 : ℝ) ^ d * ((1 / 25 : ℝ) ^ d * finePascalDamping n a p ξ) := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (25 : ℝ) ^ d * pascalDamping n p ξ :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)

/-- Multiplication by a power of two preserves nondivisibility by three. -/
theorem not_three_dvd_mul_two_pow {j ξ : ℕ} (hξ : ¬ 3 ∣ ξ) : ¬ 3 ∣ ξ * 2 ^ j := by
  have htwo : ¬ 3 ∣ 2 ^ j :=
    Nat.prime_three.coprime_iff_not_dvd.mp
      (Nat.Coprime.pow_right j (by decide : Nat.Coprime 3 2))
  simpa [Nat.prime_three.dvd_mul] using And.intro hξ htwo

/-- For fixed extra precision, the partial Pascal damping inherits the full Sec7P decay. -/
theorem finePascalDamping_add_decay :
    ∀ k : ℕ, ∀ A > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ p : ℝ, 1 / 5 ≤ p → p ≤ 3 / 5 → ∀ a ξ : ℕ, 1 ≤ a → ¬ 3 ∣ ξ →
        finePascalDamping (a + k) a p ξ ≤ C * (a : ℝ) ^ (-A) := by
  intro k A hA
  obtain ⟨C, hC, hdecay⟩ := pascalDampingDecay A hA
  refine ⟨(25 : ℝ) ^ k * C, mul_pos (by positivity) hC, ?_⟩
  intro p hp0 hp1 a ξ ha hξ
  let d := (a + k) / 2 - a / 2
  have hadiv : a / 2 ≤ (a + k) / 2 := Nat.div_le_div_right (Nat.le_add_right a k)
  have hd : a / 2 + d = (a + k) / 2 := by
    dsimp [d]
    omega
  have hdk : d ≤ k := by
    dsimp [d]
    omega
  have hpartial := finePascalDamping_le_pow_mul_pascalDamping
    (n := a + k) (a := a) (d := d) (ξ := ξ) hp0 (by linarith) hd
  have hfull := hdecay p hp0 hp1 (a + k) ξ (by omega) hξ
  have hpow : (25 : ℝ) ^ d ≤ (25 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) hdk
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hank : (a : ℝ) ≤ (a + k : ℕ) := by exact_mod_cast Nat.le_add_right a k
  have hrpow : ((a + k : ℕ) : ℝ) ^ (-A) ≤ (a : ℝ) ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos haR hank (by linarith)
  calc
    finePascalDamping (a + k) a p ξ ≤
        (25 : ℝ) ^ d * pascalDamping (a + k) p ξ := hpartial
    _ ≤ (25 : ℝ) ^ d * (C * ((a + k : ℕ) : ℝ) ^ (-A)) :=
      mul_le_mul_of_nonneg_left hfull (by positivity)
    _ ≤ (25 : ℝ) ^ k * (C * ((a + k : ℕ) : ℝ) ^ (-A)) :=
      mul_le_mul_of_nonneg_right hpow
        (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))
    _ ≤ (25 : ℝ) ^ k * (C * (a : ℝ) ^ (-A)) := by
      gcongr
    _ = ((25 : ℝ) ^ k * C) * (a : ℝ) ^ (-A) := by ring

/-- The explicit over-precision numerator sums have uniform fixed-precision polynomial decay. -/
theorem numeratorExpSum_add_decay :
    ∀ k : ℕ, ∀ A > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ j a ξ : ℕ, 1 ≤ j → j ≤ 5 * a → 5 * a ≤ 3 * j → ¬ 3 ∣ ξ →
      ‖∑ r ∈ levelSet j a,
        Complex.exp (2 * Real.pi * Complex.I *
          (((ξ * (2 ^ j * tstep^[j] r - 3 ^ a * r) : ℕ) : ℂ) /
            (3 ^ (a + k) : ℂ)))‖ ≤
        C * (j : ℝ) ^ (-A) * (levelSet j a).card := by
  intro k A hA
  obtain ⟨D, hD, hdamping⟩ := finePascalDamping_add_decay k (A + 3) (by linarith)
  let C : ℝ := D * (4 * (5 : ℝ) ^ (A + 3))
  refine ⟨C, mul_pos hD (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)), ?_⟩
  intro j a ξ hj hja haj hξ
  have hj0 : 0 < j := by omega
  have ha0 : 1 ≤ a := by omega
  have haj' : a < j := by omega
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
  have hjaR : (j : ℝ) ≤ 5 * a := by exact_mod_cast hja
  have hajR : (5 : ℝ) * a ≤ 3 * j := by exact_mod_cast haj
  have hp0 : (1 / 5 : ℝ) ≤ (a : ℝ) / j := by
    apply (le_div_iff₀ hjR).2
    nlinarith
  have hp1 : (a : ℝ) / j ≤ 3 / 5 := by
    apply (div_le_iff₀ hjR).2
    nlinarith
  have hξ' : ¬ 3 ∣ ξ * 2 ^ j := not_three_dvd_mul_two_pow hξ
  have hpartial := hdamping ((a : ℝ) / j) hp0 hp1 a (ξ * 2 ^ j) ha0 hξ'
  have hmode := norm_numeratorExpSum_le_mode_fineDamping
    (n := a + k) (ξ := ξ) hj0 (by omega) haj'
  have hpoly := succ_sq_mul_rpow_neg_add_three hA hj hja
  calc
    ‖∑ r ∈ levelSet j a,
        Complex.exp (2 * Real.pi * Complex.I *
          (((ξ * (2 ^ j * tstep^[j] r - 3 ^ a * r) : ℕ) : ℂ) /
            (3 ^ (a + k) : ℂ)))‖ ≤
      (j + 1 : ℝ) ^ 2 * (j.choose a : ℝ) *
        finePascalDamping (a + k) a ((a : ℝ) / j) (ξ * 2 ^ j) := hmode
    _ ≤ (j + 1 : ℝ) ^ 2 * (j.choose a : ℝ) *
        (D * (a : ℝ) ^ (-(A + 3))) := by
      gcongr
    _ = D * ((j + 1 : ℝ) ^ 2 * (a : ℝ) ^ (-(A + 3))) *
        (j.choose a : ℝ) := by ring
    _ ≤ D * (4 * (5 : ℝ) ^ (A + 3) * (j : ℝ) ^ (-A)) *
        (j.choose a : ℝ) := by
      gcongr
    _ = C * (j : ℝ) ^ (-A) * (levelSet j a).card := by
      rw [card_levelSet_eq_choose]
      dsimp [C]
      ring

end CollatzMoonshot.Conjugacy
