/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalReglue.Cuts
import CollatzMoonshot.AmusicalReglue.WordOrder

/-!
# Blocks and the word order

Block `b ≥ 1` holds the segments with `spine b ≤ segMin < spine (b + 1)`; block `0` those with
`segMin < spine 1`.  The word lists the blocks as `⋯ B₅ B₃ B₁ | B₀ B₂ B₄ ⋯`, each block in
decreasing order of `segMin` (`rcKey`).  A forward survivor of the glued map then lies in a
segment of block `0` or is a spine point (`survivor_mem`): a later segment of smaller minimum
exists otherwise (the spine of an even block, or the spine point `spine 0` for odd blocks).
-/

namespace CollatzMoonshot.Amusical

variable {σ : Equiv.Perm ℕ} {S : Set ℕ}

section

variable (hsp : {y | GluePt σ S y ∧ y ∈ S ∧ σ.symm y ∈ S}.Infinite) (B : ℕ → ℕ)

/-- The cut at the spine point `spine b`. -/
noncomputable def spineCut (b : ℕ) : rcCuts σ S B := ⟨spine σ S B b, Or.inl (Or.inr ⟨b, rfl⟩)⟩

theorem nextTime_spineCut (b : ℕ) : (rcCuts_isCutSet hsp B).nextTime (spineCut B b) = 1 := by
  have h1 := (rcCuts_isCutSet hsp B).nextTime_min (spineCut B b) (k := 1) one_pos (by
    simp only [Nat.cast_one, zpow_one]
    exact Or.inr ⟨_, ⟨b, rfl⟩, rfl⟩)
  have h2 := (rcCuts_isCutSet hsp B).nextTime_pos' (spineCut B b)
  omega

theorem segMin_spineCut (b : ℕ) :
    (rcCuts_isCutSet hsp B).segMin (spineCut B b) = spine σ S B b := by
  obtain ⟨r, hr, h⟩ := (rcCuts_isCutSet hsp B).segMin_mem (spineCut B b)
  rw [nextTime_spineCut hsp] at hr
  rw [← h, show r = 0 by omega]
  rfl

theorem exists_block (c : rcCuts σ S B) :
    ∃ b, (rcCuts_isCutSet hsp B).segMin c < spine σ S B (b + 1) :=
  ⟨(rcCuts_isCutSet hsp B).segMin c, lt_of_lt_of_le (Nat.lt_succ_self _)
    ((spine_strictMono hsp B).id_le _)⟩

/-- The block of a segment. -/
noncomputable def rcBlock (c : rcCuts σ S B) : ℕ := Nat.find (exists_block hsp B c)

theorem segMin_lt_block (c : rcCuts σ S B) :
    (rcCuts_isCutSet hsp B).segMin c < spine σ S B (rcBlock hsp B c + 1) :=
  Nat.find_spec (exists_block hsp B c)

theorem spine_block_le (c : rcCuts σ S B) (h : 1 ≤ rcBlock hsp B c) :
    spine σ S B (rcBlock hsp B c) ≤ (rcCuts_isCutSet hsp B).segMin c := by
  have := Nat.find_min (exists_block hsp B c) (m := rcBlock hsp B c - 1) (by
    unfold rcBlock at h ⊢; omega)
  rw [Nat.sub_add_cancel h] at this
  omega

theorem rcBlock_spineCut (b : ℕ) : rcBlock hsp B (spineCut B b) = b := by
  have hmono := spine_strictMono hsp B
  unfold rcBlock
  rw [Nat.find_eq_iff]
  refine ⟨by rw [segMin_spineCut hsp]; exact hmono (Nat.lt_succ_self b), fun n hn => ?_⟩
  rw [segMin_spineCut hsp, not_lt]
  exact hmono.monotone (by omega)

end

/-- Position of block `b` in the word `⋯ B₅ B₃ B₁ | B₀ B₂ B₄ ⋯`. -/
def blockPos (b : ℕ) : ℤ := if b % 2 = 0 then ((b / 2 : ℕ) : ℤ) else -((b / 2 : ℕ) : ℤ) - 1

section

variable (hsp : {y | GluePt σ S y ∧ y ∈ S ∧ σ.symm y ∈ S}.Infinite) (B : ℕ → ℕ)

/-- The word order key: block position, then decreasing segment minimum. -/
noncomputable def rcKey (c : rcCuts σ S B) : ℤ ×ₗ ℤ :=
  toLex (blockPos (rcBlock hsp B c), -((rcCuts_isCutSet hsp B).segMin c : ℤ))

theorem rcKey_injective : Function.Injective (rcKey hsp B) := by
  intro a b h
  have h2 := congrArg (fun p => (ofLex p).2) h
  simp only [rcKey, ofLex_toLex, neg_inj, Nat.cast_inj] at h2
  exact (rcCuts_isCutSet hsp B).segMin_injective h2

theorem rcKey_finite (a b : rcCuts σ S B) :
    {c | rcKey hsp B a ≤ rcKey hsp B c ∧ rcKey hsp B c ≤ rcKey hsp B b}.Finite := by
  set pa := blockPos (rcBlock hsp B a)
  set pb := blockPos (rcBlock hsp B b)
  let N : ℕ := (2 * pb + 1).toNat + (-2 * pa).toNat
  refine ((rcCuts_isCutSet hsp B).finite_segMin_lt (spine σ S B (N + 1))).subset ?_
  rintro c ⟨h1, h2⟩
  simp only [Set.mem_ofPred_eq]
  have h1' : pa ≤ blockPos (rcBlock hsp B c) := by
    rcases Prod.Lex.toLex_le_toLex.1 h1 with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  have h2' : blockPos (rcBlock hsp B c) ≤ pb := by
    rcases Prod.Lex.toLex_le_toLex.1 h2 with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  have hN : rcBlock hsp B c ≤ N := by
    have e1 := Int.self_le_toNat (2 * pb + 1)
    have e2 := Int.self_le_toNat (-2 * pa)
    unfold blockPos at h1' h2'
    split_ifs at h1' h2' <;> omega
  exact lt_of_lt_of_le (segMin_lt_block hsp B c)
    ((spine_strictMono hsp B).monotone (by omega))

theorem rcKey_spineCut (b : ℕ) :
    rcKey hsp B (spineCut B b) = toLex (blockPos b, -(spine σ S B b : ℤ)) := by
  simp only [rcKey, rcBlock_spineCut hsp, segMin_spineCut hsp]

theorem rcKey_exists_gt (a : rcCuts σ S B) : ∃ b, rcKey hsp B a < rcKey hsp B b := by
  refine ⟨spineCut B (2 * rcBlock hsp B a + 2), ?_⟩
  rw [rcKey_spineCut]
  refine Prod.Lex.toLex_lt_toLex.2 (Or.inl ?_)
  simp only [rcKey, ofLex_toLex, blockPos]
  split_ifs <;> omega

theorem rcKey_exists_lt (a : rcCuts σ S B) : ∃ b, rcKey hsp B b < rcKey hsp B a := by
  refine ⟨spineCut B (2 * rcBlock hsp B a + 1), ?_⟩
  rw [rcKey_spineCut]
  refine Prod.Lex.toLex_lt_toLex.2 (Or.inl ?_)
  simp only [rcKey, ofLex_toLex, blockPos]
  split_ifs <;> omega

/-- A one-cycle segment order realising the word order. -/
theorem exists_wordPerm :
    ∃ φ : Equiv.Perm (rcCuts σ S B), (∀ a b, φ.SameCycle a b) ∧
      ∀ a b, rcKey hsp B a < rcKey hsp B b → ∃ k : ℕ, 1 ≤ k ∧ (φ ^ k) a = b := by
  have _ : Nonempty (rcCuts σ S B) := ⟨spineCut B 0⟩
  obtain ⟨e, he⟩ := exists_equiv_int_of_key (rcKey hsp B) (rcKey_injective hsp B)
    (rcKey_finite hsp B) (rcKey_exists_gt hsp B) (rcKey_exists_lt hsp B)
  let φ : Equiv.Perm (rcCuts σ S B) := (e.trans (Equiv.addRight (1 : ℤ))).trans e.symm
  have hφ (k : ℕ) (a : rcCuts σ S B) : (φ ^ k) a = e.symm (e a + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, ih]
        simp [φ, add_assoc]
  refine ⟨φ, conjugate_intShift_sameCycle e, fun a b hab => ?_⟩
  have hlt := (he a b).1 hab
  refine ⟨(e b - e a).toNat, by omega, ?_⟩
  rw [hφ, Int.toNat_of_nonneg (by omega)]
  simp

/-- **Survivor classification.**  A gluable forward survivor of the glued map lies in a segment of
block `0` or is a spine point. -/
theorem survivor_mem (φ : Equiv.Perm (rcCuts σ S B))
    (hlater : ∀ a b, rcKey hsp B a < rcKey hsp B b → ∃ k : ℕ, 1 ≤ k ∧ (φ ^ k) a = b)
    {x : ℕ} (hx : GluePt σ S x)
    (hsurv : ∀ t : ℕ, x ≤ (⇑((rcCuts_isCutSet hsp B).glueWith φ))^[t] x) :
    (∃ c : rcCuts σ S B, (rcCuts_isCutSet hsp B).segMin c < spine σ S B 1 ∧
      ∃ r < (rcCuts_isCutSet hsp B).nextTime c, (σ ^ r) (c : ℕ) = x) ∨
      x ∈ Set.range (spine σ S B) := by
  set hC := rcCuts_isCutSet hsp B
  obtain ⟨k0, -, hk0⟩ := rcCuts_bwd B hx 0
  obtain ⟨c, r, hr, rfl⟩ := hC.exists_seg ⟨k0, hk0⟩
  have hmono := spine_strictMono hsp B
  have hbelow (c' : rcCuts σ S B) (h : rcKey hsp B c < rcKey hsp B c') :
      (σ ^ r) (c : ℕ) ≤ hC.segMin c' := by
    obtain ⟨k, hk, rfl⟩ := hlater c c' h
    exact hC.le_segMin_of_survivor φ hr hsurv hk
  have hle := hC.segMin_le c hr
  set β := rcBlock hsp B c with hβ
  rcases Nat.eq_zero_or_pos β with h0 | hpos
  · left
    refine ⟨c, ?_, r, hr, rfl⟩
    have := segMin_lt_block hsp B c
    rwa [← hβ, h0] at this
  have hsb : spine σ S B β ≤ hC.segMin c := spine_block_le hsp B c hpos
  rcases Nat.even_or_odd β with ⟨m, hm⟩ | ⟨m, hm⟩
  · by_cases hcs : c = spineCut B β
    · right
      have hr0 : r = 0 := by
        have := nextTime_spineCut hsp B β
        rw [← hcs] at this
        omega
      subst hr0
      rw [hcs]
      exact ⟨β, rfl⟩
    · exfalso
      have hne : hC.segMin c ≠ spine σ S B β := fun h =>
        hcs (hC.segMin_injective (h.trans (segMin_spineCut hsp B β).symm))
      have hlt : rcKey hsp B c < rcKey hsp B (spineCut B β) := by
        rw [rcKey_spineCut]
        refine Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, ?_⟩)
        simp only [ofLex_toLex]
        omega
      have := hbelow _ hlt
      rw [segMin_spineCut hsp] at this
      omega
  · exfalso
    have hlt : rcKey hsp B c < rcKey hsp B (spineCut B 0) := by
      rw [rcKey_spineCut]
      refine Prod.Lex.toLex_lt_toLex.2 (Or.inl ?_)
      simp only [rcKey, ofLex_toLex, blockPos, ← hβ]
      split_ifs <;> omega
    have h1 := hbelow _ hlt
    rw [segMin_spineCut hsp] at h1
    have h2 : spine σ S B 0 < spine σ S B β := hmono hpos
    omega

end

end CollatzMoonshot.Amusical
