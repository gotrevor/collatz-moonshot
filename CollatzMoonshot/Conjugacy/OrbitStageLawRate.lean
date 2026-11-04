/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitStageLawBasic

/-!
# The stage word law: exponential sparsity

`ExpSparse` is closed under subsets and finite unions, absorbs polynomial factors and finitely many
stages (`expSparse_of_poly`), bounds whole prefixes `[0, 2^K)` and not only stages
(`prefix_of_expSparse`), and gives stage density `0` (`tendsto_stage_of_expSparse'`).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-! ## Rates -/

/-- `(k + 1)^p ≤ 2^p (k^p + 1)`. -/
theorem succ_pow_le (p k : ℕ) : ((k : ℝ) + 1) ^ p ≤ 2 ^ p * ((k : ℝ) ^ p + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_add, one_pow]
    have : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    have : (0 : ℝ) ≤ 0 ^ p := by positivity
    nlinarith
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    calc ((k : ℝ) + 1) ^ p ≤ (2 * k) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
      _ = 2 ^ p * k ^ p := mul_pow _ _ _
      _ ≤ 2 ^ p * ((k : ℝ) ^ p + 1) := by
          have : (0 : ℝ) ≤ 2 ^ p := by positivity
          nlinarith

/-- **Polynomial factors are absorbed** by the rate `(1 + σ)/2`. -/
theorem exists_poly_pow_le (p : ℕ) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k : ℕ, ((k : ℝ) + 1) ^ p * σ ^ k ≤ D * ((1 + σ) / 2) ^ k := by
  set σ' := (1 + σ) / 2 with hσ'
  have hσ'0 : 0 < σ' := by rw [hσ']; linarith
  set r := σ / σ'
  have hr0 : 0 ≤ r := div_nonneg hσ0 hσ'0.le
  have hr1 : r < 1 := by rw [div_lt_one hσ'0, hσ']; linarith
  set g : ℕ → ℝ := fun k => 2 ^ p * ((k : ℝ) ^ p * r ^ k + r ^ k)
  have hg : Tendsto g atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one p (by rw [abs_of_nonneg hr0]; exact hr1)
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa using (h1.add h2).const_mul (2 ^ p)
  obtain ⟨D, hD⟩ := hg.bddAbove_range
  have hgD : ∀ k, g k ≤ D := fun k => hD ⟨k, rfl⟩
  have hg0 : ∀ k, 0 ≤ g k := fun k => by positivity
  refine ⟨D, le_trans (hg0 0) (hgD 0), fun k => ?_⟩
  have hσr : σ = r * σ' := by rw [div_mul_cancel₀ _ hσ'0.ne']
  calc ((k : ℝ) + 1) ^ p * σ ^ k = (((k : ℝ) + 1) ^ p * r ^ k) * σ' ^ k := by rw [hσr, mul_pow]; ring
    _ ≤ g k * σ' ^ k := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc ((k : ℝ) + 1) ^ p * r ^ k ≤ 2 ^ p * ((k : ℝ) ^ p + 1) * r ^ k :=
              mul_le_mul_of_nonneg_right (succ_pow_le p k) (by positivity)
          _ = g k := by simp only [g]; ring
    _ ≤ D * σ' ^ k := mul_le_mul_of_nonneg_right (hgD k) (by positivity)

/-- A stage holds at most `2^k` integers. -/
theorem card_stage_le (P : ℕ → Prop) [DecidablePred P] (k : ℕ) :
    (((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter P).card : ℝ) ≤ 2 ^ k := by
  have : ((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter P).card ≤ 2 ^ k :=
    le_trans (Finset.card_filter_le _ _) (by simp)
  exact_mod_cast this

open Classical in
/-- **Exponential sparsity from a bound with polynomial loss**, for all large `k`. -/
theorem expSparse_of_poly {B : Set ℕ} (C : ℝ) (p : ℕ) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (k₀ : ℕ)
    (h : ∀ k ≥ k₀, (((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (· ∈ B)).card : ℝ) ≤
      C * ((k : ℝ) + 1) ^ p * (2 * σ) ^ k) : ExpSparse B := by
  obtain ⟨D, hD0, hD⟩ := exists_poly_pow_le p hσ0 hσ1
  set σ' := (1 + σ) / 2 with hσ'
  have hσ'1 : σ' < 1 := by rw [hσ']; linarith
  have hσ'2 : 1 / 2 ≤ σ' := by rw [hσ']; linarith
  refine ⟨|C| * D + 2 ^ k₀, σ', by linarith, hσ'1, fun k => ?_⟩
  have hpos : 0 ≤ (2 * σ') ^ k := by positivity
  have h2σ : 1 ≤ 2 * σ' := by linarith
  by_cases hk : k₀ ≤ k
  · have hk' := h k hk
    have hC : C * ((k : ℝ) + 1) ^ p * (2 * σ) ^ k ≤ |C| * (((k : ℝ) + 1) ^ p * σ ^ k) * 2 ^ k := by
      have : C * ((k : ℝ) + 1) ^ p ≤ |C| * ((k : ℝ) + 1) ^ p :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      calc C * ((k : ℝ) + 1) ^ p * (2 * σ) ^ k ≤ |C| * ((k : ℝ) + 1) ^ p * (2 * σ) ^ k :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = _ := by rw [mul_pow]; ring
    calc _ ≤ |C| * (((k : ℝ) + 1) ^ p * σ ^ k) * 2 ^ k := le_trans hk' hC
      _ ≤ |C| * (D * σ' ^ k) * 2 ^ k := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hD k) (abs_nonneg C))
            (by positivity)
      _ = |C| * D * (2 * σ') ^ k := by rw [mul_pow]; ring
      _ ≤ (|C| * D + 2 ^ k₀) * (2 * σ') ^ k := by
          have : (0 : ℝ) ≤ 2 ^ k₀ := by positivity
          nlinarith
  · push Not at hk
    have h1 : (2 : ℝ) ^ k ≤ 2 ^ k₀ * (2 * σ') ^ k := by
      have : (1 : ℝ) ≤ (2 * σ') ^ k := one_le_pow₀ h2σ
      have : (2 : ℝ) ^ k ≤ 2 ^ k₀ := pow_le_pow_right₀ (by norm_num) hk.le
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
    calc _ ≤ (2 : ℝ) ^ k := card_stage_le _ k
      _ ≤ 2 ^ k₀ * (2 * σ') ^ k := h1
      _ ≤ (|C| * D + 2 ^ k₀) * (2 * σ') ^ k := by
          have : 0 ≤ |C| * D := mul_nonneg (abs_nonneg C) hD0
          nlinarith

/-- A rate in `k / N` is a rate in `k`. -/
theorem exists_pow_div_le {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {N : ℕ} (hN : 1 ≤ N) :
    ∃ σ : ℝ, 0 ≤ σ ∧ σ < 1 ∧ ∀ k : ℕ, τ ^ (k / N) ≤ τ⁻¹ * σ ^ k := by
  refine ⟨τ ^ ((1 : ℝ) / N), by positivity, ?_, fun k => ?_⟩
  · exact Real.rpow_lt_one hτ0.le hτ1 (by positivity)
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← Real.rpow_natCast (τ ^ _), ← Real.rpow_mul hτ0.le, le_inv_mul_iff₀ hτ0]
    have hfl : (k : ℝ) / N < ((k / N : ℕ) : ℝ) + 1 := by
      have := Nat.lt_div_mul_add (a := k) (b := N) (by omega)
      rw [div_lt_iff₀ hN']
      have : (k : ℝ) < ((k / N : ℕ) : ℝ) * N + N := by exact_mod_cast this
      linarith
    calc τ * τ ^ (k / N) = τ ^ (((k / N : ℕ) : ℝ) + 1) := by
          rw [Real.rpow_add_one hτ0.ne', Real.rpow_natCast]; ring
      _ ≤ τ ^ ((1 : ℝ) / N * k) := by
          refine Real.rpow_le_rpow_of_exponent_ge hτ0 hτ1.le ?_
          rw [one_div_mul_eq_div]; exact hfl.le

/-! ## Closure -/

theorem expSparse_mono {B B' : Set ℕ} (h : B ⊆ B') (hB' : ExpSparse B') : ExpSparse B := by
  classical
  obtain ⟨A, ρ, hρ0, hρ1, hA⟩ := hB'
  refine ⟨A, ρ, hρ0, hρ1, fun k => le_trans ?_ (hA k)⟩
  exact_mod_cast Finset.card_le_card fun n hn =>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, h (Finset.mem_filter.mp hn).2⟩

theorem expSparse_empty : ExpSparse ∅ := ⟨0, 0, le_refl _, by norm_num, fun k => by simp⟩

theorem expSparse_union {B₁ B₂ : Set ℕ} (h₁ : ExpSparse B₁) (h₂ : ExpSparse B₂) :
    ExpSparse (B₁ ∪ B₂) := by
  classical
  obtain ⟨A₁, ρ₁, h0₁, h1₁, hA₁⟩ := h₁
  obtain ⟨A₂, ρ₂, h0₂, h1₂, hA₂⟩ := h₂
  refine ⟨|A₁| + |A₂|, max ρ₁ ρ₂, le_max_of_le_left h0₁, max_lt h1₁ h1₂, fun k => ?_⟩
  have e1 : A₁ * (2 * ρ₁) ^ k ≤ |A₁| * (2 * max ρ₁ ρ₂) ^ k :=
    mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by positivity)
      (by linarith [le_max_left ρ₁ ρ₂]) k) (by positivity) (abs_nonneg _)
  have e2 : A₂ * (2 * ρ₂) ^ k ≤ |A₂| * (2 * max ρ₁ ρ₂) ^ k :=
    mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by positivity)
      (by linarith [le_max_right ρ₁ ρ₂]) k) (by positivity) (abs_nonneg _)
  refine le_trans (Nat.cast_le.mpr (le_trans (Finset.card_le_card ?_) (Finset.card_union_le
    ((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (· ∈ B₁))
    ((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (· ∈ B₂))))) ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union] at hn ⊢
    tauto
  · push_cast
    linarith [hA₁ k, hA₂ k]

/-- Finite unions of exponentially sparse sets are exponentially sparse. -/
theorem expSparse_biUnion_range' (J : ℕ) (B : ℕ → Set ℕ) (h : ∀ j < J, ExpSparse (B j)) :
    ExpSparse (⋃ j ∈ Finset.range J, B j) := by
  induction J with
  | zero => simpa using expSparse_empty
  | succ J ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]
    exact expSparse_union (ih fun j hj => h j (by omega)) (h J (by omega))

/-! ## Prefixes -/

/-- `∑_(k ≤ K) x^k ≤ 3 x^K` for `x ≥ 3/2`. -/
theorem geom_le_three {x : ℝ} (hx : 3 / 2 ≤ x) : ∀ K : ℕ, ∑ k ∈ Finset.range (K + 1), x ^ k ≤ 3 * x ^ K
  | 0 => by simp
  | K + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have := geom_le_three hx K
    have : 0 ≤ x ^ K := pow_nonneg (by linarith) K
    nlinarith

open Classical in
/-- **Prefixes.**  An exponentially sparse set holds at most `A (2ρ)^K` integers below `2^K`. -/
theorem prefix_of_expSparse {B : Set ℕ} (hB : ExpSparse B) :
    ∃ A ρ : ℝ, 0 ≤ A ∧ 3 / 4 ≤ ρ ∧ ρ < 1 ∧
      ∀ K : ℕ, (((Finset.range (2 ^ K)).filter (· ∈ B)).card : ℝ) ≤ A * (2 * ρ) ^ K := by
  obtain ⟨A₀, ρ₀, h0, h1, hA₀⟩ := hB
  set ρ := max ρ₀ (3 / 4)
  refine ⟨1 + 3 * |A₀|, ρ, by positivity, le_max_right _ _, max_lt h1 (by norm_num), fun K => ?_⟩
  have hsub : (Finset.range (2 ^ K)).filter (· ∈ B) ⊆ insert 0
      ((Finset.range (K + 1)).biUnion fun k => (Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (· ∈ B)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨Nat.size n, ?_, ?_⟩)
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.size_le.mpr (Finset.mem_range.mp hn1)))
      · have hs : 0 < Nat.size n := Nat.size_pos.mpr hpos
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨Nat.lt_size.mp (by omega),
          Nat.lt_size_self n⟩, hn2⟩
  have hx : 3 / 2 ≤ 2 * ρ := by linarith [le_max_right ρ₀ (3 / 4)]
  have hstage : ∀ k, A₀ * (2 * ρ₀) ^ k ≤ |A₀| * (2 * ρ) ^ k := fun k =>
    mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by positivity)
      (by linarith [le_max_left ρ₀ (3 / 4)]) k) (by positivity) (abs_nonneg _)
  calc (((Finset.range (2 ^ K)).filter (· ∈ B)).card : ℝ)
      ≤ ((insert 0 ((Finset.range (K + 1)).biUnion fun k =>
          (Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (· ∈ B))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ 1 + ∑ k ∈ Finset.range (K + 1),
          (((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (· ∈ B)).card : ℝ) := by
        have := le_trans (Finset.card_insert_le (0 : ℕ) _) (Nat.add_le_add_right
          (Finset.card_biUnion_le (s := Finset.range (K + 1))
            (t := fun k => (Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (· ∈ B))) 1)
        have h' := (Nat.cast_le (α := ℝ)).mpr this
        push_cast at h'
        linarith
    _ ≤ 1 + ∑ k ∈ Finset.range (K + 1), |A₀| * (2 * ρ) ^ k := by
        gcongr with k
        exact le_trans (hA₀ k) (hstage k)
    _ = 1 + |A₀| * ∑ k ∈ Finset.range (K + 1), (2 * ρ) ^ k := by rw [Finset.mul_sum]
    _ ≤ 1 + |A₀| * (3 * (2 * ρ) ^ K) := by
        gcongr
        exact geom_le_three hx K
    _ ≤ (1 + 3 * |A₀|) * (2 * ρ) ^ K := by
        have : (1 : ℝ) ≤ (2 * ρ) ^ K := one_le_pow₀ (by linarith)
        nlinarith [abs_nonneg A₀]

/-! ## Density -/

open Classical in
/-- **Density.**  A property that eventually forces membership in an exponentially sparse set has
stage density `0`. -/
theorem tendsto_stage_of_expSparse' {B : Set ℕ} (hB : ExpSparse B) (P : ℕ → Prop) (k₀ : ℕ)
    (hP : ∀ k ≥ k₀, ∀ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), P n → n ∈ B) :
    Tendsto (fun k : ℕ => (((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter P).card : ℝ) / 2 ^ (k - 1))
      atTop (𝓝 0) := by
  obtain ⟨A, ρ, hρ0, hρ1, hA⟩ := hB
  have hlim : Tendsto (fun k : ℕ => 2 * A * ρ ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul (2 * A)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun k => by positivity) ?_
  filter_upwards [eventually_ge_atTop (max k₀ 1)] with k hk
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hsub : (Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter P ⊆
      (Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (· ∈ B) := fun n hn => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨h1, hP k (le_trans (le_max_left _ _) hk) n h1 h2⟩
  have hc : (((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter P).card : ℝ) ≤ A * (2 * ρ) ^ k :=
    le_trans (by exact_mod_cast Finset.card_le_card hsub) (hA k)
  have h2 : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ A * (2 * ρ) ^ k := hc
    _ = 2 * A * ρ ^ k * 2 ^ (k - 1) := by rw [mul_pow, h2]; ring

end CollatzMoonshot.Conjugacy
