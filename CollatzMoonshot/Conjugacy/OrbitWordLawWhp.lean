/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawTerras
import CollatzMoonshot.Conjugacy.OrbitWordLawStage

/-!
# The orbit word law: Terras at one scale

* `probPeriodicLe_holds` proves `ProbPeriodicLe`: an event that sees only `N mod 2^(3 n₀)` has
  `winLaw x`-probability at most its uniform probability over odd residues (at most twice its
  proportion among all residues), plus Tao's integral-test error `K 2^(−3 n₀)`.
* `winGoodWhp_holds` proves `WinGoodWhp`: the bad residues are covered by boundedly many bad
  blocks of length `≈ δ η log₂ x / 8`, each of proportion `O(1 / block length)` by Chebyshev.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-! ## Transfer by the integral test -/

open Classical in
/-- The uniform law on odd residues gives an event at most twice its proportion. -/
theorem unifOddMod_expect_le (M : ℕ) (hM : 1 ≤ M) (S : Set ℕ) :
    (unifOddMod M).expect (Set.indicator {z : ZMod (2 ^ M) | z.val ∈ S} 1) ≤
      2 * (((Finset.range (2 ^ M)).filter (· ∈ S)).card : ℝ) / 2 ^ M := by
  have : NeZero (2 ^ M) := ⟨by positivity⟩
  set A : Set (ZMod (2 ^ M)) := {z | z.val ∈ S} with hA
  unfold PMF.expect
  rw [tsum_fintype]
  have hterm : ∀ z : ZMod (2 ^ M), ((unifOddMod M) z).toReal * A.indicator 1 z ≤
      if z ∈ A then ((2 : ℝ) ^ (M - 1))⁻¹ else 0 := by
    intro z
    rw [unifOddMod_apply_of_pos M hM z]
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz, if_pos hz]
      split_ifs
      · simp
      · simp
    · rw [Set.indicator_of_notMem hz, if_neg hz, mul_zero]
  refine le_trans (Finset.sum_le_sum fun z _ => hterm z) ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (· ∈ A)).card ≤ ((Finset.range (2 ^ M)).filter (· ∈ S)).card := by
    refine Finset.card_le_card_of_injOn (fun z => z.val) (fun z hz => ?_)
      (fun z _ w _ h => ZMod.val_injective _ h)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hA] at hz
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨ZMod.val_lt z, hz⟩
  have hcR : ((Finset.univ.filter (· ∈ A)).card : ℝ) ≤
      (((Finset.range (2 ^ M)).filter (· ∈ S)).card : ℝ) := by exact_mod_cast hcard
  have hpow : ((2 : ℝ) ^ (M - 1))⁻¹ = 2 / 2 ^ M := by
    obtain ⟨d, rfl⟩ : ∃ d, M = d + 1 := ⟨M - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [hpow, mul_div_assoc', mul_comm]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- **Transfer by the integral test** (`ProbPeriodicLe`). -/
theorem probPeriodicLe_holds : ProbPeriodicLe := by
  classical
  refine ⟨max X_intTestLogUnif X_nZeroPos, fun x hx S hS => ?_⟩
  have hx1 : X_intTestLogUnif ≤ x := le_trans (le_max_left _ _) hx
  have hxz : X_nZeroPos ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 ≤ x := le_trans (by unfold X_nZeroPos; positivity) hxz
  set M := 3 * nZero x with hMdef
  have hM : 1 ≤ M := by have := nZero_pos_atX x hxz; omega
  have hdtv := integral_test_logUnif_atCX x hx1 (x ^ alpha) (Set.mem_insert _ _)
  have hw : logUnifOdd (x ^ alpha) ((x ^ alpha) ^ alpha) = winLaw x := by
    rw [winLaw, ← Real.rpow_mul hx0, pow_two]
  rw [hw] at hdtv
  set f : ℕ → ZMod (2 ^ M) := fun N => (N : ZMod (2 ^ M)) with hf
  set A : Set (ZMod (2 ^ M)) := {z | z.val ∈ S} with hA
  have hcomp : (Set.indicator A (1 : ZMod (2 ^ M) → ℝ)) ∘ f = Set.indicator S 1 := by
    funext N
    simp only [Function.comp_apply]
    have hmem : f N ∈ A ↔ N ∈ S := by
      simp only [hf, hA, Set.mem_ofPred_eq, ZMod.val_natCast]
      exact hS N
    by_cases h : N ∈ S
    · rw [Set.indicator_of_mem (hmem.mpr h), Set.indicator_of_mem h]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => h (hmem.mp h')), Set.indicator_of_notMem h]
  have h1 : (winLaw x).expect (Set.indicator S 1) =
      ((winLaw x).map f).expect (Set.indicator A 1) := by
    rw [PMF.expect_map_of_nonneg (winLaw x) f (Set.indicator A 1)
      fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) z, hcomp]
  have hq : PMF.map (fun N : ZMod (2 ^ M) => N) (do let a ← winLaw x; pure (a : ZMod (2 ^ M))) =
      (winLaw x).map f := by
    rw [show (fun N : ZMod (2 ^ M) => N) = id from rfl, PMF.map_id]
    rfl
  rw [hq] at hdtv
  have h2 := PMF.abs_expect_indicator_sub_le_dTV ((winLaw x).map f) (unifOddMod M) A
  have h3 := unifOddMod_expect_le M hM S
  rw [h1]
  linarith [(abs_le.mp h2).2]

/-! ## Terras at one scale -/

open Classical in
/-- **The bad residues are covered by bad blocks.**  With `K` blocks of length `b` covering the first
`2 Λ` letters, the residues mod `2^M` with a bad window number at most `K · 32 |u| 2^M / (δ² b)`. -/
theorem card_not_winGood_le (u : List Bool) {δ : ℝ} (hδ : 0 < δ) {H Λ M K b : ℕ} (hb : 0 < b)
    (hK : 2 * Λ ≤ K * b) (h8 : 8 * (b : ℝ) ≤ δ * H) (hfit : K * b + u.length ≤ M) :
    (((Finset.range (2 ^ M)).filter (· ∈ {r | ¬ WinGood u δ H Λ r})).card : ℝ) ≤
      K * (32 * u.length * 2 ^ M / (δ ^ 2 * b)) := by
  have hsub : (Finset.range (2 ^ M)).filter (· ∈ {r | ¬ WinGood u δ H Λ r}) ⊆
      (Finset.range K).biUnion fun k => (Finset.range (2 ^ M)).filter
        fun r => δ / 4 * b < |wdev u r (k * b) b| := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Set.mem_ofPred_eq] at hr ⊢
    by_contra hcon
    refine hr.2 (winGoodOfBlocks_holds u δ H Λ K b r hδ hb hK h8 fun k hk => ?_)
    by_contra hk'
    exact hcon ⟨k, hk, hr.1, lt_of_not_ge hk'⟩
  have hcard := Finset.card_le_card hsub
  have hcard' : (((Finset.range (2 ^ M)).filter (· ∈ {r | ¬ WinGood u δ H Λ r})).card : ℝ) ≤
      ∑ k ∈ Finset.range K, (((Finset.range (2 ^ M)).filter
        fun r => δ / 4 * b < |wdev u r (k * b) b|).card : ℝ) := by
    exact_mod_cast le_trans hcard Finset.card_biUnion_le
  refine le_trans hcard' ?_
  have hterm : ∀ k ∈ Finset.range K, (((Finset.range (2 ^ M)).filter
      fun r => δ / 4 * b < |wdev u r (k * b) b|).card : ℝ) ≤
        32 * u.length * 2 ^ M / (δ ^ 2 * b) := by
    intro k hk
    have hkK : k < K := Finset.mem_range.mp hk
    have hfk : k * b + b + u.length ≤ M := by
      have : (k + 1) * b ≤ K * b := Nat.mul_le_mul_right b hkK
      nlinarith
    have := cardBadBlockLe_holds u M (k * b) b (δ / 4) hfk (by positivity) hb
    have he : 2 * (u.length : ℝ) * 2 ^ M / ((δ / 4) ^ 2 * b) =
        32 * u.length * 2 ^ M / (δ ^ 2 * b) := by
      have : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
      field_simp
      ring
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `2 lam x ≤ nZero x`: the window cap is at most half of Tao's `n₀`. -/
theorem two_mul_lam_le_nZero (x : ℝ) : 2 * lam x ≤ nZero x := by
  unfold lam nZero
  rcases le_or_gt (Real.logb 2 x / 20) 0 with h | h
  · rw [Nat.floor_eq_zero.mpr (by linarith)]
    simp
  · refine Nat.le_floor ?_
    have h1 := Nat.floor_le h.le
    have he : Real.log x / (10 * Real.log 2) = 2 * (Real.logb 2 x / 20) := by
      unfold Real.logb
      have : Real.log 2 ≠ 0 := by positivity
      field_simp
      ring
    rw [he]
    push_cast
    linarith

/-- The window cap tends to infinity. -/
theorem tendsto_lam : Tendsto lam atTop atTop := by
  unfold lam
  refine tendsto_nat_floor_atTop.comp ?_
  refine Tendsto.atTop_div_const (by norm_num) ?_
  exact Real.tendsto_logb_atTop (by norm_num)

/-- `2^(−3 n₀(x)) → 0`. -/
theorem tendsto_two_rpow_neg_nZero :
    Tendsto (fun x => (2 : ℝ) ^ (-(3 * (nZero x : ℝ)))) atTop (𝓝 0) := by
  have hn : Tendsto nZero atTop atTop := by
    unfold nZero
    refine tendsto_nat_floor_atTop.comp ?_
    exact Real.tendsto_log_atTop.atTop_div_const (by positivity)
  have h3 : Tendsto (fun x => 3 * nZero x) atTop atTop :=
    (tendsto_id.const_mul_atTop' (by norm_num)).comp hn
  have h2 := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt
    (show (1 : ℝ) < 2 by norm_num))).comp h3
  refine h2.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_neg (by norm_num), show (3 * (nZero x : ℝ)) = ((3 * nZero x : ℕ) : ℝ) by
    push_cast; ring, Real.rpow_natCast]

open Classical in
/-- **Terras at one scale** (`WinGoodWhp`).  With a fixed number `K` of blocks of length
`b = 2 Λ / K + 1`, the bad residues have proportion `O(K² / Λ)`, and Tao's integral test
transfers this to `winLaw x`. -/
theorem winGoodWhp_holds : WinGoodWhp := by
  intro u δ η hδ hη
  obtain ⟨X₁, hX₁⟩ := probPeriodicLe_holds
  set K : ℕ := ⌈8 / (5 * (δ * η))⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := Nat.le_add_left 1 _
  have hKR : 8 / (5 * (δ * η)) ≤ (K : ℝ) - 1 := by
    rw [hKdef]
    push_cast
    linarith [Nat.le_ceil (8 / (5 * (δ * η)))]
  set A : ℝ := 64 * (K : ℝ) ^ 2 * u.length / δ ^ 2 with hA
  have hbound : Tendsto (fun x => A / (2 * (lam x : ℝ) + 1) +
      K_intTest * (2 : ℝ) ^ (-(3 * (nZero x : ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x => A / (2 * (lam x : ℝ) + 1)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      refine tendsto_atTop_add_const_right _ 1 ?_
      exact (tendsto_natCast_atTop_atTop.comp tendsto_lam).const_mul_atTop (by norm_num)
    have h2 := tendsto_two_rpow_neg_nZero.const_mul K_intTest
    rw [mul_zero] at h2
    simpa using h1.add h2
  refine squeeze_zero' (Eventually.of_forall fun x => prob_nonneg _ _) ?_ hbound
  have hn : Tendsto nZero atTop atTop := by
    unfold nZero
    refine tendsto_nat_floor_atTop.comp ?_
    exact Real.tendsto_log_atTop.atTop_div_const (by positivity)
  have hL : Tendsto (fun x => Real.logb 2 x) atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  filter_upwards [eventually_ge_atTop X₁, eventually_ge_atTop 1,
    hn.eventually_ge_atTop (K + u.length),
    hL.eventually_ge_atTop (16 / (δ * η))] with x hxX hx1 hnx hLx
  set Λ := lam x with hΛ
  set H := hgt η x with hH
  set M := 3 * nZero x with hM
  set b : ℕ := 2 * Λ / K + 1 with hbdef
  have hb : 0 < b := Nat.succ_pos _
  have hKb : 2 * Λ < K * b := by
    rw [hbdef, mul_add, mul_one, mul_comm K]
    exact Nat.lt_div_mul_add (by omega)
  have hKb' : K * b ≤ 2 * Λ + K := by
    rw [hbdef, mul_add, mul_one]
    have := Nat.mul_div_le (2 * Λ) K
    linarith [mul_comm K (2 * Λ / K)]
  have h2Λ := two_mul_lam_le_nZero x
  have hfit : K * b + u.length ≤ M := by omega
  have hmod : 2 * Λ + u.length ≤ M := by omega
  -- the block length is at most `δ H / 8`
  have hL0 : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1
  have hlamR : (Λ : ℝ) ≤ Real.logb 2 x / 20 := lam_le hx1
  have hHR : η * Real.logb 2 x ≤ H := Nat.le_ceil _
  have h8 : 8 * (b : ℝ) ≤ δ * H := by
    have hbR : (b : ℝ) ≤ 2 * Λ / K + 1 := by
      rw [hbdef]
      push_cast
      have := Nat.cast_div_le (α := ℝ) (m := 2 * Λ) (n := K)
      push_cast at this
      linarith
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
    have hδη : 0 < δ * η := mul_pos hδ hη
    -- `8 b ≤ 16 Λ / K + 8 ≤ δ η L / 2 + δ η L / 2`
    have hΛK : 16 * (Λ : ℝ) / K ≤ δ * η * Real.logb 2 x / 2 := by
      rw [div_le_iff₀ hKpos]
      have hK' : 8 / (5 * (δ * η)) * (δ * η) ≤ ((K : ℝ) - 1) * (δ * η) :=
        mul_le_mul_of_nonneg_right hKR hδη.le
      have he : 8 / (5 * (δ * η)) * (δ * η) = 8 / 5 := by field_simp
      rw [he] at hK'
      nlinarith
    have h8L : 8 ≤ δ * η * Real.logb 2 x / 2 := by
      have := mul_le_mul_of_nonneg_left hLx hδη.le
      rw [mul_div_cancel₀ _ hδη.ne'] at this
      linarith
    have hδH : δ * η * Real.logb 2 x ≤ δ * H := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hHR hδ.le
    have : 8 * (b : ℝ) ≤ 16 * Λ / K + 8 := by
      have : 8 * (2 * (Λ : ℝ) / K) = 16 * Λ / K := by ring
      linarith
    linarith
  have hS : ∀ n, n % 2 ^ M ∈ {r | ¬ WinGood u δ H Λ r} ↔ n ∈ {r | ¬ WinGood u δ H Λ r} := by
    intro n
    simp only [Set.mem_ofPred_eq]
    exact not_congr (winGoodModIff_holds u δ H Λ M hmod n)
  have hP := hX₁ x hxX {r | ¬ WinGood u δ H Λ r} hS
  rw [← hM] at hP
  have hc := card_not_winGood_le u hδ hb hKb.le h8 hfit
  refine le_trans hP (add_le_add ?_ le_rfl)
  -- `2 · K · 32 |u| 2^M / (δ² b) / 2^M ≤ A / (2 Λ + 1)`
  have hM0 : (0 : ℝ) < 2 ^ M := by positivity
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hKbR : 2 * (Λ : ℝ) + 1 ≤ K * b := by exact_mod_cast hKb
  have hKR0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  refine le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (le_trans (le_of_eq ?_) hc) (by norm_num)) hM0.le) ?_
  · congr
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  calc 2 * (K * (32 * u.length * 2 ^ M / (δ ^ 2 * b))) / 2 ^ M
      = 64 * K ^ 2 * u.length / (δ ^ 2 * (K * b)) := by
        field_simp
        ring
    _ ≤ 64 * K ^ 2 * u.length / (δ ^ 2 * (2 * (Λ : ℝ) + 1)) := by
        gcongr
    _ = A / (2 * (Λ : ℝ) + 1) := by
        rw [hA]
        field_simp

end CollatzMoonshot.Conjugacy
