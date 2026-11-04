/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitStageLawTerras
import CollatzMoonshot.Conjugacy.OrbitWordLawTerras

/-!
# The stage word law: P1, the one-window good event

For a class `c < |u|`, the windows at `c + j |u|` see disjoint blocks of letters, and exactly one
residue mod `2^|u|` matches `u` (`cardMatchOne_holds`).  So Chernoff applies to the matches and to the
non-matches (`classTail`), and with `OddTail` and `SufTail` at `ℓ₀ = k / 10` the event `GoodZero` fails
on an exponentially sparse set (`expSparse_not_goodZero'`).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- A window at `0` sees only `x mod 2^L`. -/
theorem windowMatch_zero_mod (g : ℕ → Bool) (L : ℕ) :
    ∀ x : ℕ, WindowMatch g L 0 x ↔ WindowMatch g L 0 (x % 2 ^ L) := fun x => by
  refine forall₂_congr fun s hs => ?_
  rw [zero_add, accWord_congr_mod s (s := x % 2 ^ L)]
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : s + 1 ≤ L))]

theorem not_windowMatch_zero_mod (g : ℕ → Bool) (L : ℕ) :
    ∀ x : ℕ, ¬ WindowMatch g L 0 x ↔ ¬ WindowMatch g L 0 (x % 2 ^ L) := fun x => by
  exact not_congr (windowMatch_zero_mod g L x)

/-- Exactly one residue mod `2^|u|` matches `u`. -/
theorem card_match_one (u : List Bool) :
    ((Finset.range (2 ^ u.length)).filter (WindowMatch (uLet u) u.length 0)).card = 1 := by
  have := cardMatchOne_holds u u.length 0 (by omega)
  rw [Nat.sub_self, pow_zero] at this
  exact this

theorem card_not_match (u : List Bool) :
    ((Finset.range (2 ^ u.length)).filter fun x => ¬ WindowMatch (uLet u) u.length 0 x).card =
      2 ^ u.length - 1 := by
  have := Finset.card_filter_add_card_filter_not (s := Finset.range (2 ^ u.length))
    (WindowMatch (uLet u) u.length 0)
  rw [card_match_one, Finset.card_range] at this
  omega

open Classical in
/-- **The class tail.**  `ClassGood u η k` fails for at most `2 |u| (k + 1) 2^k τ^k` residues. -/
theorem classTail (u : List Bool) {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ < 1 ∧ ∀ k : ℕ,
      (((Finset.range (2 ^ k)).filter fun r => ¬ ClassGood u η k r).card : ℝ) ≤
        2 * u.length * ((k : ℝ) + 1) * 2 ^ k * τ ^ k := by
  set L := u.length
  set p : ℝ := (1 / 2 : ℝ) ^ L
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set κ := η * η ^ 2 * p / (1 + η)
  have hκ : 0 < κ := by positivity
  refine ⟨Real.exp (-κ), (Real.exp_pos _).le,
    by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith), fun k => ?_⟩
  rcases Nat.eq_zero_or_pos L with hL | hL
  · have : (Finset.range (2 ^ k)).filter (fun r => ¬ ClassGood u η k r) = ∅ := by
      refine Finset.filter_false_of_mem fun r _ => ?_
      push Not
      intro c hc
      omega
    rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  have hpL : p ≤ 1 / 2 := by
    calc p = (1 / 2) ^ L := rfl
      _ ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hL
      _ = 1 / 2 := by norm_num
  set Y : ℕ → ℕ → ℕ → ℕ := fun c q r => blkCnt (WindowMatch (uLet u) L 0) L c q r
  set Y' : ℕ → ℕ → ℕ → ℕ := fun c q r => blkCnt (fun x => ¬ WindowMatch (uLet u) L 0 x) L c q r
  set I := (Finset.range L ×ˢ Finset.range (k + 1)).filter fun cq =>
    cq.1 + cq.2 * L ≤ k ∧ η * k ≤ cq.2
  set E1 : ℕ × ℕ → Finset ℕ := fun cq => (Finset.range (2 ^ k)).filter fun r =>
    (p + η) * (cq.2 : ℝ) ≤ Y cq.1 cq.2 r
  set E2 : ℕ × ℕ → Finset ℕ := fun cq => (Finset.range (2 ^ k)).filter fun r =>
    ((1 - p) + η) * (cq.2 : ℝ) ≤ Y' cq.1 cq.2 r
  have hsub : (Finset.range (2 ^ k)).filter (fun r => ¬ ClassGood u η k r) ⊆
      I.biUnion E1 ∪ I.biUnion E2 := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
    unfold ClassGood at hr2
    push Not at hr2
    obtain ⟨c, hc, q, hq1, hq2, hbad⟩ := hr2
    have hq3 : q < k + 1 := by
      have : q ≤ q * u.length := Nat.le_mul_of_pos_right q hL
      omega
    have hcI : (c, q) ∈ I := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hc, Finset.mem_range.mpr hq3⟩, hq1, hq2⟩
    have hsum : Y c q r + Y' c q r = q := blkCnt_add_not _ L c q r
    have hsumR : (Y c q r : ℝ) + (Y' c q r : ℝ) = q := by exact_mod_cast hsum
    rcases lt_abs.mp hbad with h | h
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(c, q), hcI,
        Finset.mem_filter.mpr ⟨hr1, ?_⟩⟩)
      show (p + η) * (q : ℝ) ≤ Y c q r
      have : (Y c q r : ℝ) = blkCnt (WindowMatch (uLet u) u.length 0) u.length c q r := rfl
      linarith
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(c, q), hcI,
        Finset.mem_filter.mpr ⟨hr1, ?_⟩⟩)
      show ((1 - p) + η) * (q : ℝ) ≤ Y' c q r
      have : (Y c q r : ℝ) = blkCnt (WindowMatch (uLet u) u.length 0) u.length c q r := rfl
      linarith
  have hexp : ∀ q : ℕ, η * k ≤ q → ∀ p' : ℝ, p ≤ p' →
      Real.exp (-(q * η ^ 2 * p' / (1 + η))) ≤ Real.exp (-κ) ^ k := by
    intro q hq p' hp'
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have h1 : 0 < 1 + η := by linarith
    have h2 : (k : ℝ) * κ ≤ q * η ^ 2 * p' / (1 + η) := by
      have e : (k : ℝ) * κ = (k : ℝ) * (η * η ^ 2 * p) / (1 + η) := by simp only [κ]; ring
      rw [e]
      refine div_le_div_of_nonneg_right ?_ h1.le
      have : 0 ≤ η ^ 2 := by positivity
      have : (k : ℝ) * η ≤ q := by linarith
      calc (k : ℝ) * (η * η ^ 2 * p) = ((k : ℝ) * η) * (η ^ 2 * p) := by ring
        _ ≤ q * (η ^ 2 * p') := mul_le_mul this (by nlinarith) (by positivity) (by positivity)
        _ = q * η ^ 2 * p' := by ring
    linarith
  have hE1 : ∀ cq ∈ I, ((E1 cq).card : ℝ) ≤ 2 ^ k * Real.exp (-κ) ^ k := by
    intro cq hcq
    obtain ⟨_, hfit, hq⟩ := Finset.mem_filter.mp hcq
    have hM : ∑ r ∈ Finset.range (2 ^ k), (1 + η) ^ Y cq.1 cq.2 r ≤ 2 ^ k * (1 + p * η) ^ cq.2 := by
      rw [sum_pow_blkCnt_le _ (windowMatch_zero_mod _ L) cq.1 cq.2 k hfit, card_match_one]
      simp [p, one_div_pow]
    refine le_trans (card_ge_le_of_mgf _ _ cq.2 hp0.le hη hM)
      (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine le_trans (Real.exp_le_exp.mpr ?_) (hexp cq.2 hq (1 - p) (by linarith))
    exact le_refl _
  have hE2 : ∀ cq ∈ I, ((E2 cq).card : ℝ) ≤ 2 ^ k * Real.exp (-κ) ^ k := by
    intro cq hcq
    obtain ⟨_, hfit, hq⟩ := Finset.mem_filter.mp hcq
    have hM : ∑ r ∈ Finset.range (2 ^ k), (1 + η) ^ Y' cq.1 cq.2 r ≤
        2 ^ k * (1 + (1 - p) * η) ^ cq.2 := by
      rw [sum_pow_blkCnt_le _ (not_windowMatch_zero_mod _ L) cq.1 cq.2 k hfit, card_not_match]
      have hc : ((2 ^ u.length - 1 : ℕ) : ℝ) / 2 ^ L = 1 - p := by
        rw [Nat.cast_sub Nat.one_le_two_pow]
        push_cast
        simp only [p, L, one_div_pow, one_div]
        field_simp
      rw [hc, show (1 : ℝ) + η - 1 = η by ring]
    refine le_trans (card_ge_le_of_mgf _ _ cq.2 (by linarith) hη hM)
      (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine le_trans (Real.exp_le_exp.mpr ?_) (hexp cq.2 hq p le_rfl)
    rw [sub_sub_cancel]
  have hIcard : (I.card : ℝ) ≤ L * ((k : ℝ) + 1) := by
    have : I.card ≤ L * (k + 1) := le_trans (Finset.card_filter_le _ _) (by simp)
    exact_mod_cast this
  calc (((Finset.range (2 ^ k)).filter fun r => ¬ ClassGood u η k r).card : ℝ)
      ≤ ((I.biUnion E1 ∪ I.biUnion E2).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ cq ∈ I, ((E1 cq).card : ℝ) + ∑ cq ∈ I, ((E2 cq).card : ℝ) := by
        have := le_trans (Finset.card_union_le _ _)
          (Nat.add_le_add (Finset.card_biUnion_le (s := I) (t := E1))
            (Finset.card_biUnion_le (s := I) (t := E2)))
        exact_mod_cast this
    _ ≤ ∑ _cq ∈ I, 2 ^ k * Real.exp (-κ) ^ k + ∑ _cq ∈ I, 2 ^ k * Real.exp (-κ) ^ k :=
        add_le_add (Finset.sum_le_sum hE1) (Finset.sum_le_sum hE2)
    _ = 2 * I.card * (2 ^ k * Real.exp (-κ) ^ k) := by simp; ring
    _ ≤ 2 * (L * ((k : ℝ) + 1)) * (2 ^ k * Real.exp (-κ) ^ k) := by
        gcongr
    _ = 2 * u.length * ((k : ℝ) + 1) * 2 ^ k * Real.exp (-κ) ^ k := by ring

open Classical in
/-- **P1.**  The one-window good event fails on an exponentially sparse set. -/
theorem expSparse_not_goodZero' (u : List Bool) {η γ : ℝ} (hη : 0 < η) (hγ : 0 < γ) :
    ExpSparse {n | ¬ GoodZero u η γ n} := by
  obtain ⟨τc, hτc0, hτc1, hτc⟩ := classTail u hη
  obtain ⟨τo, hτo0, hτo1, hτo⟩ := oddTail_holds' γ hγ
  obtain ⟨τs, hτs0, hτs1, hτs⟩ := sufTail_holds'
  obtain ⟨σs, hσs0, hσs1, hσs⟩ := exists_pow_div_le hτs0 hτs1 (by norm_num : 1 ≤ 10)
  set σ := max τc (max τo σs)
  have hσ0 : 0 ≤ σ := le_max_of_le_left hτc0
  have hσ1 : σ < 1 := max_lt hτc1 (max_lt hτo1 hσs1)
  refine expSparse_of_poly (2 * u.length + 1 + τs⁻¹) 1 hσ0 hσ1 1 fun k hk => ?_
  set I := Finset.Ico (2 ^ (k - 1)) (2 ^ k)
  have hsub : I.filter (· ∈ {n | ¬ GoodZero u η γ n}) ⊆ (I.filter fun n => ¬ ClassGood u η k n) ∪
      (I.filter fun n => ¬ OddLow γ k n) ∪ (I.filter fun n => ¬ SufGood (k / 10) k n) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hn
    have hn' := Finset.mem_Ico.mp h1
    have hsize : Nat.size n = k := size_of_mem_stage hk hn'.1 hn'.2
    simp only [Set.mem_ofPred_eq, GoodZero, hsize] at h2
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have hk1 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpow : ∀ x : ℝ, 0 ≤ x → x ≤ σ → (2 * x) ^ k ≤ (2 * σ) ^ k := fun x hx hxσ =>
    pow_le_pow_left₀ (by positivity) (by linarith) k
  have t1 := le_trans (card_stage_le_range (fun n => ¬ ClassGood u η k n) k) (hτc k)
  have t2 := le_trans (card_stage_le_range (fun n => ¬ OddLow γ k n) k) (hτo k)
  have t3 := le_trans (card_stage_le_range (fun n => ¬ SufGood (k / 10) k n) k) (hτs k (k / 10))
  have e1 : 2 * (u.length : ℝ) * ((k : ℝ) + 1) * 2 ^ k * τc ^ k ≤
      2 * u.length * ((k : ℝ) + 1) ^ 1 * (2 * σ) ^ k := by
    rw [pow_one, mul_assoc _ (2 ^ k), ← mul_pow]
    exact mul_le_mul_of_nonneg_left (hpow τc hτc0 (le_max_left _ _)) (by positivity)
  have e2 : (2 : ℝ) ^ k * τo ^ k ≤ 1 * ((k : ℝ) + 1) ^ 1 * (2 * σ) ^ k := by
    rw [← mul_pow, pow_one, one_mul]
    calc (2 * τo) ^ k ≤ (2 * σ) ^ k :=
          hpow τo hτo0 (le_trans (le_max_left _ _) (le_max_right _ _))
      _ ≤ ((k : ℝ) + 1) * (2 * σ) ^ k := le_mul_of_one_le_left (by positivity) (by linarith)
  have e3 : ((k : ℝ) + 1) * 2 ^ k * τs ^ (k / 10) ≤ τs⁻¹ * ((k : ℝ) + 1) ^ 1 * (2 * σ) ^ k := by
    calc ((k : ℝ) + 1) * 2 ^ k * τs ^ (k / 10) ≤ ((k : ℝ) + 1) * 2 ^ k * (τs⁻¹ * σs ^ k) :=
          mul_le_mul_of_nonneg_left (hσs k) (by positivity)
      _ = τs⁻¹ * ((k : ℝ) + 1) ^ 1 * (2 * σs) ^ k := by rw [mul_pow]; ring
      _ ≤ τs⁻¹ * ((k : ℝ) + 1) ^ 1 * (2 * σ) ^ k :=
          mul_le_mul_of_nonneg_left (hpow σs hσs0
            (le_trans (le_max_right _ _) (le_max_right _ _))) (by positivity)
  rw [Finset.filter_congr_decidable]
  refine le_trans (Nat.cast_le.mpr (le_trans (Finset.card_le_card hsub)
    (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)))) ?_
  push_cast
  calc ((I.filter fun n => ¬ ClassGood u η k n).card : ℝ) +
        ((I.filter fun n => ¬ OddLow γ k n).card : ℝ) +
        ((I.filter fun n => ¬ SufGood (k / 10) k n).card : ℝ)
    _ ≤ 2 * u.length * ((k : ℝ) + 1) ^ 1 * (2 * σ) ^ k + 1 * ((k : ℝ) + 1) ^ 1 * (2 * σ) ^ k +
        τs⁻¹ * ((k : ℝ) + 1) ^ 1 * (2 * σ) ^ k := by
        linarith [le_trans t1 e1, le_trans t2 e2, le_trans t3 e3]
    _ = (2 * u.length + 1 + τs⁻¹) * ((k : ℝ) + 1) ^ 1 * (2 * σ) ^ k := by ring

end CollatzMoonshot.Conjugacy
