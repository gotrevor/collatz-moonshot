/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalContinuousReversor.Cylinder

/-!
# Finite counting for continuous amusical reversors

This module codes backward orbit prefixes by ternary words and counts the majority events used
in the finite proof that a residue-determined reversing map cannot have linear growth.
-/

namespace CollatzMoonshot.Amusical

def continuousRawStepSym (n : ℤ) : Fin 3 :=
  if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else 2

theorem continuousRawStepSym_inv_eq_iff (x y : ℤ) :
    continuousRawStepSym (amusicalInv x) = continuousRawStepSym (amusicalInv y) ↔
      x % 3 = y % 3 := by
  unfold continuousRawStepSym amusicalInv
  split_ifs <;> simp_all <;> omega

def continuousBackwardStepWord (L : ℕ) (n : ℤ) (i : Fin L) : Fin 3 :=
  continuousRawStepSym (amusicalInv^[i.val + 1] n)

theorem continuousBackwardStepWord_succ (L : ℕ) (n : ℤ) :
    continuousBackwardStepWord (L + 1) n =
      Fin.cons (continuousRawStepSym (amusicalInv n))
        (continuousBackwardStepWord L (amusicalInv n)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [continuousBackwardStepWord]
  · simp [continuousBackwardStepWord, Function.iterate_succ_apply]

theorem continuousBackwardStepWord_eq_of_modEq (L : ℕ) {x y : ℤ}
    (hxy : x ≡ y [ZMOD 3 ^ L]) :
    continuousBackwardStepWord L x = continuousBackwardStepWord L y := by
  induction L generalizing x y with
  | zero => exact Subsingleton.elim _ _
  | succ L ih =>
      rw [continuousBackwardStepWord_succ, continuousBackwardStepWord_succ, Fin.cons_inj]
      have hthree : (3 : ℤ) ∣ 3 ^ (L + 1) := ⟨3 ^ L, by rw [pow_succ']⟩
      have hhead : x ≡ y [ZMOD 3] := hxy.of_dvd hthree
      have htail := amusicalInv_iterate_modEq_three L 1 hxy
      simp only [Function.iterate_one] at htail
      exact ⟨(continuousRawStepSym_inv_eq_iff x y).mpr hhead, ih htail⟩

theorem continuous_pow_three_dvd_sub_of_word_eq (L : ℕ) {x y : ℤ}
    (hxy : continuousBackwardStepWord L x = continuousBackwardStepWord L y) :
    (3 : ℤ) ^ L ∣ x - y := by
  induction L generalizing x y with
  | zero => simp
  | succ L ih =>
      rw [continuousBackwardStepWord_succ, continuousBackwardStepWord_succ, Fin.cons_inj] at hxy
      have hmod : x ≡ y [ZMOD 3] := (continuousRawStepSym_inv_eq_iff x y).mp hxy.1
      obtain ⟨q, hq⟩ := Int.modEq_iff_add_fac.mp hmod
      have htail : (3 : ℤ) ^ L ∣ amusicalInv x - amusicalInv y := ih hxy.2
      let d : ℤ := if x % 3 = 0 then 2 else 4
      have hy : amusicalInv y = amusicalInv x + d * q := by
        rw [hq, amusicalInv_add_three_mul]
        simp [d]
      have hdq : (3 : ℤ) ^ L ∣ d * q := by
        rw [hy] at htail
        simpa only [sub_add_cancel_left, Int.dvd_neg] using htail
      have hcop : IsCoprime ((3 : ℤ) ^ L) d := by
        apply IsCoprime.pow_left
        dsimp only [d]
        split
        · exact ⟨1, -1, by norm_num⟩
        · exact ⟨-1, 1, by norm_num⟩
      obtain ⟨r, hr⟩ := hcop.dvd_of_dvd_mul_left hdq
      refine ⟨-r, ?_⟩
      rw [hq, pow_succ', hr]
      ring

noncomputable def continuousBackwardStepWordEquiv (L : ℕ) :
    Fin (3 ^ L) ≃ (Fin L → Fin 3) := by
  let f : Fin (3 ^ L) → (Fin L → Fin 3) := fun r =>
    continuousBackwardStepWord L (r.val : ℤ)
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  refine ⟨?_, by simp⟩
  intro a b hab
  have hd : (3 : ℤ) ^ L ∣ (a.val : ℤ) - b.val :=
    continuous_pow_three_dvd_sub_of_word_eq L hab
  have hlt : |(a.val : ℤ) - b.val| < (3 : ℤ) ^ L := by
    have ha : (a.val : ℤ) < (3 : ℤ) ^ L := by exact_mod_cast a.isLt
    have hb : (b.val : ℤ) < (3 : ℤ) ^ L := by exact_mod_cast b.isLt
    rcases le_total a.val b.val with hab | hba
    · have habz : (a.val : ℤ) ≤ (b.val : ℤ) := by exact_mod_cast hab
      rw [abs_of_nonpos (sub_nonpos.mpr habz)]
      omega
    · have hbaz : (b.val : ℤ) ≤ (a.val : ℤ) := by exact_mod_cast hba
      rw [abs_of_nonneg (sub_nonneg.mpr hbaz)]
      omega
  have hz := Int.eq_zero_of_abs_lt_dvd hd hlt
  exact Fin.ext (by omega)

noncomputable def continuousWordBlocksEquiv (L w : ℕ) :
    (Fin (L * w) → Fin 3) ≃ (Fin L → Fin w → Fin 3) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl (Fin 3))).trans
    (Equiv.curry (Fin L) (Fin w) (Fin 3))

noncomputable def continuousAllBlocksEquiv (L w : ℕ) (P : (Fin w → Fin 3) → Prop) :
    {f : Fin (L * w) → Fin 3 // ∀ i, P (continuousWordBlocksEquiv L w f i)} ≃
      (Fin L → {u : Fin w → Fin 3 // P u}) := by
  let e : {g : Fin L → Fin w → Fin 3 // ∀ i, P (g i)} ≃
      (Fin L → {u : Fin w → Fin 3 // P u}) :=
    { toFun := fun g i => ⟨g.val i, g.property i⟩
      invFun := fun h => ⟨fun i => (h i).val, fun i => (h i).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ((continuousWordBlocksEquiv L w).subtypeEquiv fun _ => Iff.rfl).trans e

theorem continuous_card_all_blocks (L w : ℕ) (P : (Fin w → Fin 3) → Prop)
    [DecidablePred P] :
    Fintype.card {f : Fin (L * w) → Fin 3 //
      ∀ i, P (continuousWordBlocksEquiv L w f i)} =
      ((Finset.univ.filter P).card) ^ L := by
  classical
  calc
    _ = Fintype.card (Fin L → {u : Fin w → Fin 3 // P u}) :=
      Fintype.card_congr (continuousAllBlocksEquiv L w P)
    _ = Fintype.card {u : Fin w → Fin 3 // P u} ^ L :=
      Fintype.card_pi_const _ L
    _ = ((Finset.univ.filter P).card) ^ L := by
      rw [Fintype.card_subtype]

theorem continuousWordBlocks_backwardStepWord (L w : ℕ) (n : ℤ) (i : Fin L) :
    continuousWordBlocksEquiv L w (continuousBackwardStepWord (L * w) n) i =
      continuousBackwardStepWord w (amusicalInv^[i.val * w] n) := by
  have hcomm : amusicalInv^[w * i.val] (amusicalInv n) =
      amusicalInv (amusicalInv^[w * i.val] n) := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  funext j
  simp [continuousWordBlocksEquiv, continuousBackwardStepWord, Function.iterate_add_apply,
    Function.iterate_succ_apply, Nat.add_assoc, Nat.mul_comm, hcomm]

theorem continuous_inv_iterate_modEq_product_of_word_eq (c d : ℕ) {x y : ℤ}
    (hword : continuousBackwardStepWord (c + d) x = continuousBackwardStepWord (c + d) y) :
    amusicalInv^[c] x ≡ amusicalInv^[c] y [ZMOD (2 : ℤ) ^ c * 3 ^ d] := by
  have hdiv : (3 : ℤ) ^ (c + d) ∣ x - y :=
    continuous_pow_three_dvd_sub_of_word_eq (c + d) hword
  have hmod : x ≡ y [ZMOD (3 : ℤ) ^ (d + c)] := by
    apply Int.modEq_of_dvd
    rw [Nat.add_comm]
    obtain ⟨q, hq⟩ := hdiv
    exact ⟨-q, by linear_combination -hq⟩
  have hthree : amusicalInv^[c] x ≡ amusicalInv^[c] y [ZMOD (3 : ℤ) ^ d] :=
    amusicalInv_iterate_modEq_three d c hmod
  obtain ⟨q, hq⟩ := hdiv
  have hy : y = x + (3 : ℤ) ^ c * (-(3 : ℤ) ^ d * q) := by
    rw [pow_add] at hq
    nlinarith
  have htwo : amusicalInv^[c] x ≡ amusicalInv^[c] y [ZMOD (2 : ℤ) ^ c] := by
    rw [hy, amusicalInv_iterate_add_pow_three_mul_exact c c le_rfl]
    simp only [Nat.sub_self, pow_zero, one_mul]
    rw [Int.modEq_iff_add_fac]
    rw [amusicalBackwardMultiplier_eq]
    refine ⟨(2 : ℤ) ^ amusicalBackwardFourCount c x * (-(3 : ℤ) ^ d * q), ?_⟩
    rw [pow_add]
    ring
  apply (Int.modEq_and_modEq_iff_modEq_mul ?_).mp
  · exact ⟨htwo, hthree⟩
  · simpa using Nat.Coprime.pow c d (by norm_num : Nat.Coprime 2 3)

noncomputable def continuousBlockOutput (φ : ℤ → ℤ) (c d : ℕ)
    (u : Fin (c + d) → Fin 3) : Fin 3 :=
  let r := (continuousBackwardStepWordEquiv (c + d)).symm u
  continuousRawStepSym (φ (amusicalInv^[c] (r.val : ℤ)))

theorem continuousBlockOutput_backwardStepWord (φ : ℤ → ℤ) (c d : ℕ)
    (htable : ∀ x y : ℤ, x ≡ y [ZMOD (2 : ℤ) ^ c * 3 ^ d] →
      continuousRawStepSym (φ x) = continuousRawStepSym (φ y)) (n : ℤ) :
    continuousBlockOutput φ c d (continuousBackwardStepWord (c + d) n) =
      continuousRawStepSym (φ (amusicalInv^[c] n)) := by
  let u := continuousBackwardStepWord (c + d) n
  let r := (continuousBackwardStepWordEquiv (c + d)).symm u
  have hr : continuousBackwardStepWord (c + d) (r.val : ℤ) = u := by
    change continuousBackwardStepWordEquiv (c + d) r = u
    exact Equiv.apply_symm_apply _ _
  apply htable
  apply continuous_inv_iterate_modEq_product_of_word_eq c d
  simpa only [u] using hr

def continuousStepBit (s : Fin 3) : Bool := decide (s ≠ 0)

theorem continuous_exists_majority_bit (w : ℕ) (F : (Fin w → Fin 3) → Bool) :
    ∃ b a, a = (Finset.univ.filter fun u => F u = b).card ∧ 3 ^ w < 2 * a := by
  classical
  let a₀ := (Finset.univ.filter fun u => F u = false).card
  let a₁ := (Finset.univ.filter fun u => F u = true).card
  have hsum : a₀ + a₁ = 3 ^ w := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin w → Fin 3))) (fun u => F u = true)
    simpa [a₀, a₁, add_comm] using h
  have hodd : 3 ^ w % 2 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rcases le_total a₁ a₀ with hle | hle
  · exact ⟨false, a₀, rfl, by omega⟩
  · exact ⟨true, a₁, rfl, by omega⟩

theorem continuous_count_eq_card_subtype_fin (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    Nat.count P N = Fintype.card {r : Fin N // P r.val} := by
  rw [Fintype.card_subtype]
  simpa using (card_filter_fin_lt_eq_count N N le_rfl P).symm

def continuousInputEvent (φ : ℤ → ℤ) (c d : ℕ) (b : Bool) (L : ℕ) (n : ℕ) : Prop :=
  ∀ i : Fin L, continuousStepBit
    (continuousRawStepSym (φ (amusicalInv^[c] (amusicalInv^[i.val * (c + d)] (n : ℤ))))) = b

theorem continuousInputEvent_iff_blocks (φ : ℤ → ℤ) (c d : ℕ)
    (htable : ∀ x y : ℤ, x ≡ y [ZMOD (2 : ℤ) ^ c * 3 ^ d] →
      continuousRawStepSym (φ x) = continuousRawStepSym (φ y)) (b : Bool) (L n : ℕ) :
    continuousInputEvent φ c d b L n ↔ ∀ i : Fin L,
      continuousStepBit (continuousBlockOutput φ c d
        (continuousWordBlocksEquiv L (c + d)
          (continuousBackwardStepWord (L * (c + d)) (n : ℤ)) i)) = b := by
  constructor <;> intro h i
  · rw [continuousWordBlocks_backwardStepWord,
      continuousBlockOutput_backwardStepWord φ c d htable]
    exact h i
  · have hi := h i
    rw [continuousWordBlocks_backwardStepWord,
      continuousBlockOutput_backwardStepWord φ c d htable] at hi
    exact hi

theorem continuousInputEvent_mod (φ : ℤ → ℤ) (c d : ℕ)
    (htable : ∀ x y : ℤ, x ≡ y [ZMOD (2 : ℤ) ^ c * 3 ^ d] →
      continuousRawStepSym (φ x) = continuousRawStepSym (φ y)) (b : Bool) (L n : ℕ) :
    continuousInputEvent φ c d b L n ↔
      continuousInputEvent φ c d b L (n % 3 ^ (L * (c + d))) := by
  rw [continuousInputEvent_iff_blocks φ c d htable,
    continuousInputEvent_iff_blocks φ c d htable]
  have hmod : (n : ℤ) ≡ (n % 3 ^ (L * (c + d)) : ℕ)
      [ZMOD (3 : ℤ) ^ (L * (c + d))] := by
    convert (Int.mod_modEq (n : ℤ) ((3 : ℤ) ^ (L * (c + d)))).symm using 1
    push_cast
    rfl
  rw [continuousBackwardStepWord_eq_of_modEq _ hmod]

open Classical in
theorem continuous_count_inputEvent (φ : ℤ → ℤ) (c d : ℕ)
    (htable : ∀ x y : ℤ, x ≡ y [ZMOD (2 : ℤ) ^ c * 3 ^ d] →
      continuousRawStepSym (φ x) = continuousRawStepSym (φ y)) (b : Bool) (L a : ℕ)
    (ha : a = (Finset.univ.filter fun u =>
      continuousStepBit (continuousBlockOutput φ c d u) = b).card) :
    Nat.count (continuousInputEvent φ c d b L) (3 ^ (L * (c + d))) = a ^ L := by
  let E := continuousBackwardStepWordEquiv (L * (c + d))
  let Q : (Fin (L * (c + d)) → Fin 3) → Prop := fun f =>
    ∀ i, continuousStepBit (continuousBlockOutput φ c d
      (continuousWordBlocksEquiv L (c + d) f i)) = b
  have hpred : ∀ r : Fin (3 ^ (L * (c + d))),
      continuousInputEvent φ c d b L r.val ↔ Q (E r) := by
    intro r
    change (∀ i : Fin L, continuousStepBit (continuousRawStepSym (φ
      (amusicalInv^[c] (amusicalInv^[i.val * (c + d)] (r.val : ℤ))))) = b) ↔ _
    change _ ↔ ∀ i : Fin L, continuousStepBit (continuousBlockOutput φ c d
      (continuousWordBlocksEquiv L (c + d)
        (continuousBackwardStepWord (L * (c + d)) (r.val : ℤ)) i)) = b
    constructor <;> intro h i
    · rw [continuousWordBlocks_backwardStepWord,
        continuousBlockOutput_backwardStepWord φ c d htable]
      exact h i
    · have hi := h i
      rw [continuousWordBlocks_backwardStepWord,
        continuousBlockOutput_backwardStepWord φ c d htable] at hi
      exact hi
  rw [continuous_count_eq_card_subtype_fin]
  calc
    Fintype.card {r : Fin (3 ^ (L * (c + d))) //
        continuousInputEvent φ c d b L r.val} =
        Fintype.card {f : Fin (L * (c + d)) → Fin 3 // Q f} :=
      Fintype.card_congr (E.subtypeEquiv hpred)
    _ = (Finset.univ.filter fun u =>
        continuousStepBit (continuousBlockOutput φ c d u) = b).card ^ L := by
      simpa only [Q] using continuous_card_all_blocks L (c + d)
        (fun u => continuousStepBit (continuousBlockOutput φ c d u) = b)
    _ = a ^ L := by rw [ha]

noncomputable def continuousFixedCoordinatesEquiv {I J B : Type*} [Fintype I]
    [Fintype J] [DecidableEq J] (e : I → J) (b : B) :
    {f : J → B // ∀ i, f (e i) = b} ≃ ({j : J // j ∉ Set.range e} → B) where
  toFun f j := f.val j.val
  invFun g := ⟨fun j => if hj : j ∈ Set.range e then b else g ⟨j, hj⟩,
    fun i => by simp⟩
  left_inv f := by
    ext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      simp [f.property]
    · simp [hj]
  right_inv g := by
    funext j
    simp [j.property]

theorem continuous_card_fixedCoordinates {I J B : Type*} [Fintype I] [Fintype J]
    [Fintype B] [DecidableEq J] [DecidableEq B] (e : I → J)
    (he : Function.Injective e) (b : B) :
    Fintype.card {f : J → B // ∀ i, f (e i) = b} =
      Fintype.card B ^ (Fintype.card J - Fintype.card I) := by
  classical
  calc
    _ = Fintype.card ({j : J // j ∉ Set.range e} → B) :=
      Fintype.card_congr (continuousFixedCoordinatesEquiv e b)
    _ = Fintype.card B ^ Fintype.card {j : J // j ∉ Set.range e} := by
      rw [Fintype.card_fun]
    _ = Fintype.card B ^ (Fintype.card J - Fintype.card I) := by
      rw [Fintype.card_subtype_compl]
      congr 2
      exact (Fintype.card_congr (Equiv.ofInjective e he)).symm

theorem continuous_card_filter_fixedCoordinates {I J B : Type*} [Fintype I]
    [Fintype J] [Fintype B] [DecidableEq J] [DecidableEq B] (e : I → J)
    (he : Function.Injective e) (b : B)
    [DecidablePred (fun f : J → B => ∀ i, f (e i) = b)] :
    (Finset.univ.filter fun f : J → B => ∀ i, f (e i) = b).card =
      Fintype.card B ^ (Fintype.card J - Fintype.card I) := by
  classical
  rw [← Fintype.card_subtype]
  calc
    _ = Fintype.card ({j : J // j ∉ Set.range e} → B) :=
      Fintype.card_congr (continuousFixedCoordinatesEquiv e b)
    _ = Fintype.card B ^ Fintype.card {j : J // j ∉ Set.range e} := by
      rw [Fintype.card_fun]
    _ = Fintype.card B ^ (Fintype.card J - Fintype.card I) := by
      rw [Fintype.card_subtype_compl]
      congr 2
      exact (Fintype.card_congr (Equiv.ofInjective e he)).symm

theorem continuousStepBit_rawStepSym (n : ℤ) :
    continuousStepBit (continuousRawStepSym n) = decide (n % 2 ≠ 0) := by
  unfold continuousStepBit continuousRawStepSym
  split_ifs <;> simp_all

def continuousOutputLength (c d L : ℕ) : ℕ := c + L * (c + d)

def continuousOutputIndex (c d L : ℕ) (hw : 0 < c + d) (i : Fin L) :
    Fin (continuousOutputLength c d L) := by
  refine ⟨c + i.val * (c + d), ?_⟩
  unfold continuousOutputLength
  have hi : i.val * (c + d) < L * (c + d) :=
    (Nat.mul_lt_mul_right hw).2 i.isLt
  omega

theorem continuousOutputIndex_injective (c d L : ℕ) (hw : 0 < c + d) :
    Function.Injective (continuousOutputIndex c d L hw) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  simp only [continuousOutputIndex] at hv
  apply Nat.mul_right_cancel hw
  omega

def continuousOutputEvent (c d : ℕ) (b : Bool) (L : ℕ) (n : ℕ) : Prop :=
  ∀ i : Fin L, continuousStepBit
    (continuousRawStepSym (amusical^[c] (amusical^[i.val * (c + d)] (n : ℤ)))) = b

theorem continuousOutputEvent_iff_forwardWord (c d : ℕ) (b : Bool) (L : ℕ)
    (hw : 0 < c + d) (n : ℕ) :
    continuousOutputEvent c d b L n ↔ ∀ i : Fin L,
      amusicalForwardWord (continuousOutputLength c d L) n
        (continuousOutputIndex c d L hw i) = b := by
  simp only [continuousOutputEvent, amusicalForwardWord, continuousStepBit_rawStepSym]
  apply forall_congr'
  intro i
  change decide (amusical^[c] (amusical^[i.val * (c + d)] (n : ℤ)) % 2 ≠ 0) = b ↔
    decide (amusical^[c + i.val * (c + d)] (n : ℤ) % 2 ≠ 0) = b
  rw [Function.iterate_add_apply]

theorem continuous_count_forwardWord_pred (N : ℕ) (P : (Fin N → Bool) → Prop)
    [DecidablePred P] :
    Nat.count (fun r : ℕ => P (amusicalForwardWord N r)) (4 ^ N) =
      (Finset.univ.filter P).card * 2 ^ N := by
  classical
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_sum_card_fiberwise
    (f := fun r : ℕ => amusicalForwardWord N r) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  calc
    _ = ∑ w ∈ (Finset.univ : Finset (Fin N → Bool)),
        if P w then 2 ^ N else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.filter_filter]
      by_cases hw : P w
      · rw [if_pos hw, ← count_amusicalForwardWord_eq N w,
          Nat.count_eq_card_filter_range]
        congr 1
        apply Finset.filter_congr
        intro r _
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hw, h⟩⟩
      · rw [if_neg hw, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro r _ ⟨hP, heq⟩
        exact hw (heq ▸ hP)
    _ = (Finset.univ.filter P).card * 2 ^ N := by
      rw [← Finset.sum_filter]
      simp

open Classical in
theorem continuous_count_outputEvent_mul (c d : ℕ) (b : Bool) (L : ℕ)
    (hw : 0 < c + d) :
    Nat.count (continuousOutputEvent c d b L) (4 ^ continuousOutputLength c d L) * 2 ^ L =
      4 ^ continuousOutputLength c d L := by
  let N := continuousOutputLength c d L
  let e : Fin L → Fin N := continuousOutputIndex c d L hw
  let P : (Fin N → Bool) → Prop := fun f => ∀ i, f (e i) = b
  have he : Function.Injective e := continuousOutputIndex_injective c d L hw
  have hcard : (Finset.univ.filter P).card = 2 ^ (N - L) := by
    simpa [P] using continuous_card_filter_fixedCoordinates e he b
  have hevent : ∀ n, continuousOutputEvent c d b L n ↔
      P (amusicalForwardWord N n) := by
    intro n
    simpa only [N, P, e] using continuousOutputEvent_iff_forwardWord c d b L hw n
  have hcount : Nat.count (continuousOutputEvent c d b L) (4 ^ N) =
      2 ^ (N - L) * 2 ^ N := by
    calc
      _ = Nat.count (fun n => P (amusicalForwardWord N n)) (4 ^ N) :=
        (count_congr' hevent) (4 ^ N)
      _ = (Finset.univ.filter P).card * 2 ^ N :=
        continuous_count_forwardWord_pred N P
      _ = 2 ^ (N - L) * 2 ^ N := by rw [hcard]
  have hLN : L ≤ N := by
    dsimp only [N, continuousOutputLength]
    have hw1 : 1 ≤ c + d := hw
    nlinarith
  rw [hcount, ← pow_add, ← pow_add]
  rw [show N - L + N + L = N + N by omega]
  change 2 ^ (N + N) = 4 ^ N
  rw [show N + N = 2 * N by omega, pow_mul]
  norm_num

theorem continuousOutputEvent_mod (c d : ℕ) (b : Bool) (L : ℕ)
    (hw : 0 < c + d) (n : ℕ) :
    continuousOutputEvent c d b L n ↔
      continuousOutputEvent c d b L (n % 4 ^ continuousOutputLength c d L) := by
  rw [continuousOutputEvent_iff_forwardWord c d b L hw,
    continuousOutputEvent_iff_forwardWord c d b L hw]
  rw [amusicalForwardWord_natCast_mod]

def continuousOutputEventInt (c d : ℕ) (b : Bool) (L : ℕ) (z : ℤ) : Prop :=
  ∀ i : Fin L, continuousStepBit
    (continuousRawStepSym (amusical^[c] (amusical^[i.val * (c + d)] z))) = b

theorem continuousStepBit_rawStepSym_neg (z : ℤ) :
    continuousStepBit (continuousRawStepSym (-z)) = continuousStepBit (continuousRawStepSym z) := by
  rw [continuousStepBit_rawStepSym, continuousStepBit_rawStepSym]
  congr 1
  simp only [ne_eq, ← Int.dvd_iff_emod_eq_zero]
  simp

theorem continuous_amusical_iterate_neg (t : ℕ) (z : ℤ) :
    amusical^[t] (-z) = -(amusical^[t] z) := by
  induction t generalizing z with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, amusical_neg]

theorem continuousOutputEventInt_neg (c d : ℕ) (b : Bool) (L : ℕ) (z : ℤ) :
    continuousOutputEventInt c d b L (-z) ↔ continuousOutputEventInt c d b L z := by
  unfold continuousOutputEventInt
  apply forall_congr'
  intro i
  rw [continuous_amusical_iterate_neg, continuous_amusical_iterate_neg,
    continuousStepBit_rawStepSym_neg]

theorem continuousOutputEventInt_natAbs (c d : ℕ) (b : Bool) (L : ℕ) (z : ℤ) :
    continuousOutputEventInt c d b L z ↔ continuousOutputEvent c d b L z.natAbs := by
  change continuousOutputEventInt c d b L z ↔
    continuousOutputEventInt c d b L (z.natAbs : ℤ)
  rw [Int.natCast_natAbs]
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz]
  · rw [abs_of_nonpos (by omega), continuousOutputEventInt_neg]

theorem continuous_count_le_two_count_of_injective_natAbs (φ : ℤ → ℤ)
    (hφ : Function.Injective φ) (C D : ℕ)
    (hgrowth : ∀ z : ℤ, |φ z| ≤ C * |z| + D)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hmap : ∀ n, P n → Q (φ n).natAbs) (X : ℕ) :
    Nat.count P X ≤ 2 * Nat.count Q (C * X + D + 1) := by
  classical
  let S := (Finset.range X).filter P
  let T := (Finset.range (C * X + D + 1)).filter Q
  let Spos := S.filter fun n : ℕ => 0 ≤ φ (n : ℤ)
  let Sneg := S.filter fun n : ℕ => φ (n : ℤ) < 0
  have hsplit : Spos.card + Sneg.card = S.card := by
    have h := Finset.card_filter_add_card_filter_not (s := S)
      (fun n : ℕ => 0 ≤ φ (n : ℤ))
    simpa [Spos, Sneg, not_le] using h
  have hpos : Spos.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => (φ n).natAbs)
    · intro n hn
      change n ∈ Spos at hn
      change (φ (n : ℤ)).natAbs ∈ T
      simp only [Spos, S, Finset.mem_filter, Finset.mem_range] at hn
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hmap n hn.1.2⟩
      have hg := hgrowth (n : ℤ)
      simp only [abs_of_nonneg (Int.natCast_nonneg n)] at hg
      have hg' : (φ (n : ℤ)).natAbs ≤ C * n + D := by
        have hgZ : ((φ (n : ℤ)).natAbs : ℤ) ≤ ((C * n + D : ℕ) : ℤ) := by
          rw [Int.natCast_natAbs]
          push_cast
          exact hg
        exact_mod_cast hgZ
      nlinarith
    · intro n hn m hm heq
      change n ∈ Spos at hn
      change m ∈ Spos at hm
      simp only [Spos, S, Finset.mem_filter, Finset.mem_range] at hn hm
      have hval : φ (n : ℤ) = φ (m : ℤ) := calc
        φ (n : ℤ) = |φ (n : ℤ)| := (abs_of_nonneg hn.2).symm
        _ = ((φ (n : ℤ)).natAbs : ℤ) :=
          (Int.natCast_natAbs (φ (n : ℤ))).symm
        _ = ((φ (m : ℤ)).natAbs : ℤ) := by exact_mod_cast heq
        _ = |φ (m : ℤ)| := Int.natCast_natAbs (φ (m : ℤ))
        _ = φ (m : ℤ) := abs_of_nonneg hm.2
      exact_mod_cast hφ hval
  have hneg : Sneg.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => (φ n).natAbs)
    · intro n hn
      change n ∈ Sneg at hn
      change (φ (n : ℤ)).natAbs ∈ T
      simp only [Sneg, S, Finset.mem_filter, Finset.mem_range] at hn
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hmap n hn.1.2⟩
      have hg := hgrowth (n : ℤ)
      simp only [abs_of_nonneg (Int.natCast_nonneg n)] at hg
      have hg' : (φ (n : ℤ)).natAbs ≤ C * n + D := by
        have hgZ : ((φ (n : ℤ)).natAbs : ℤ) ≤ ((C * n + D : ℕ) : ℤ) := by
          rw [Int.natCast_natAbs]
          push_cast
          exact hg
        exact_mod_cast hgZ
      nlinarith
    · intro n hn m hm heq
      change n ∈ Sneg at hn
      change m ∈ Sneg at hm
      simp only [Sneg, S, Finset.mem_filter, Finset.mem_range] at hn hm
      have hn : φ (n : ℤ) ≤ 0 := by omega
      have hm : φ (m : ℤ) ≤ 0 := by omega
      have hnegEq : -φ (n : ℤ) = -φ (m : ℤ) := calc
        -φ (n : ℤ) = |φ (n : ℤ)| := (abs_of_nonpos hn).symm
        _ = ((φ (n : ℤ)).natAbs : ℤ) :=
          (Int.natCast_natAbs (φ (n : ℤ))).symm
        _ = ((φ (m : ℤ)).natAbs : ℤ) := by exact_mod_cast heq
        _ = |φ (m : ℤ)| := Int.natCast_natAbs (φ (m : ℤ))
        _ = -φ (m : ℤ) := abs_of_nonpos hm
      have hval : φ (n : ℤ) = φ (m : ℤ) := neg_injective hnegEq
      exact_mod_cast hφ hval
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  change S.card ≤ 2 * T.card
  omega

theorem continuous_nat_bernoulli_mul (x : ℕ) : ∀ j,
    x ^ j * (x + j) ≤ x * (x + 1) ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ i ih =>
    have hstep : x ^ (i + 1) * (x + (i + 1)) ≤
        (x ^ i * (x + i)) * (x + 1) := by
      have hexp : (x ^ i * (x + i)) * (x + 1) =
          x ^ (i + 1) * (x + i) + x ^ i * (x + i) := by ring
      rw [hexp]
      have h1 : x ^ (i + 1) * (x + (i + 1)) =
          x ^ (i + 1) * (x + i) + x ^ (i + 1) := by ring
      rw [h1]
      have h2 : x ^ (i + 1) ≤ x ^ i * (x + i) := by
        calc
          x ^ (i + 1) = x ^ i * x := by ring
          _ ≤ x ^ i * (x + i) := Nat.mul_le_mul_left _ (by omega)
      omega
    calc
      x ^ (i + 1) * (x + (i + 1)) ≤ (x ^ i * (x + i)) * (x + 1) := hstep
      _ ≤ (x * (x + 1) ^ i) * (x + 1) := Nat.mul_le_mul_right _ ih
      _ = x * (x + 1) ^ (i + 1) := by ring

theorem continuous_const_mul_pow_lt_pow {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) (c : ℕ) :
    c * x ^ (c * x) < y ^ (c * x) := by
  set j := c * x with hj
  have hxpos : 0 < x := hx
  have hb : x ^ j * (x + j) ≤ x * (x + 1) ^ j := continuous_nat_bernoulli_mul x j
  have hy : (x + 1) ^ j ≤ y ^ j := Nat.pow_le_pow_left (by omega) j
  have h1 : x ^ j * (x + j) ≤ x * y ^ j :=
    le_trans hb (Nat.mul_le_mul_left x hy)
  have h2 : x * (c * x ^ j) < x ^ j * (x + j) := by
    have he : x ^ j * (x + j) = x ^ j * x * (1 + c) := by rw [hj]; ring
    have hl : x * (c * x ^ j) = x ^ j * x * c := by ring
    rw [he, hl]
    exact mul_lt_mul_of_pos_left (by omega) (by positivity)
  exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le h2 h1)

end CollatzMoonshot.Amusical
