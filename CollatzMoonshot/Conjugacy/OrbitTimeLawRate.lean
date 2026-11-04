/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitHeightSharp

/-!
# The time law: the stage events at a rate

`timeLaw_upper` runs the chain over a number of scales growing with `x`, so the `Tendsto`s of
`winGoodWhp_holds`, `dTV_chain` and `stage_whp` are replaced by rates.

* Terras at one scale fails with probability `O(1 / log x)` (`winGood_prob_le_rate`): the proof of
  `winGoodWhp_holds` gives `A / (2 lam x + 1) + K 2^(−3 n₀(x))`.
* The chain distance at `x_j` is at most `∑_(i<j) C_stab log(x_(i+1))^(−c_stab)`
  (`dTV_chain_le`), by `dTV_chain_step`.
* With `κ = min c_stab 1`, `log(x_j)^(−κ) = (α^κ)^j log(x)^(−κ)` grows geometrically along the
  chain, so every sum is dominated by its last scale (`chainFail_prob_le_holds`).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-! ## Terras at one scale, at a rate -/

open Classical in
/-- **Terras at one scale, with its bound** (the proof of `winGoodWhp_holds`). -/
theorem winGood_prob_eventually_le (u : List Bool) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ x in atTop, (winLaw x).expect
      (Set.indicator {N | ¬ WinGood u δ (hgt η x) (lam x) N} 1) ≤
        A / (2 * (lam x : ℝ) + 1) + K_intTest * (2 : ℝ) ^ (-(3 * (nZero x : ℝ))) := by
  obtain ⟨X₁, hX₁⟩ := probPeriodicLe_holds
  set K : ℕ := ⌈8 / (5 * (δ * η))⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := Nat.le_add_left 1 _
  have hKR : 8 / (5 * (δ * η)) ≤ (K : ℝ) - 1 := by
    rw [hKdef]
    push_cast
    linarith [Nat.le_ceil (8 / (5 * (δ * η)))]
  set A : ℝ := 64 * (K : ℝ) ^ 2 * u.length / δ ^ 2 with hA
  refine ⟨A, by positivity, ?_⟩
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


/-- `2 lam x + 1 ≥ log x / 20` once `log x ≥ 20`. -/
theorem log_div_le_lam {x : ℝ} (hx : 20 ≤ Real.log x) : Real.log x / 20 ≤ 2 * (lam x : ℝ) + 1 := by
  have h := lam_ge x
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hl2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hb : Real.log x ≤ Real.logb 2 x := by
    unfold Real.logb
    rw [le_div_iff₀ hl2']
    nlinarith
  linarith

/-- `2^(−3 n₀(x)) ≤ 10 / log x` once `log x ≥ 20`. -/
theorem two_rpow_neg_nZero_le {x : ℝ} (hx : 20 ≤ Real.log x) :
    (2 : ℝ) ^ (-(3 * (nZero x : ℝ))) ≤ 10 / Real.log x := by
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hl2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn : Real.log x / 10 - 1 ≤ nZero x := by
    unfold nZero
    have h1 : Real.log x / 10 ≤ Real.log x / (10 * Real.log 2) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
    have h2 := Nat.sub_one_lt_floor (Real.log x / (10 * Real.log 2))
    linarith
  have hp : (3 * (nZero x : ℝ)) + 1 ≤ 2 ^ (3 * nZero x) := by
    have : 3 * nZero x + 1 ≤ 2 ^ (3 * nZero x) := Nat.lt_two_pow_self
    exact_mod_cast this
  rw [show (3 * (nZero x : ℝ)) = ((3 * nZero x : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg (by norm_num), Real.rpow_natCast, ← one_div,
    div_le_div_iff₀ (by positivity) (by linarith)]
  linarith

/-- **Terras at one scale fails with probability `O(1 / log x)`.** -/
theorem winGood_prob_le_rate (u : List Bool) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in atTop, (winLaw x).expect
      (Set.indicator {N | ¬ WinGood u δ (hgt η x) (lam x) N} 1) ≤ C / Real.log x := by
  obtain ⟨A, hA, hev⟩ := winGood_prob_eventually_le u hδ hη
  have hK : 0 ≤ K_intTest := by unfold K_intTest; norm_num
  refine ⟨20 * A + 10 * K_intTest, by positivity, ?_⟩
  filter_upwards [hev, Real.tendsto_log_atTop.eventually_ge_atTop 20] with x hx hlx
  have hl0 : 0 < Real.log x := by linarith
  have h1 : A / (2 * (lam x : ℝ) + 1) ≤ 20 * A / Real.log x := by
    calc A / (2 * (lam x : ℝ) + 1) ≤ A / (Real.log x / 20) :=
          div_le_div_of_nonneg_left hA (by positivity) (log_div_le_lam hlx)
      _ = 20 * A / Real.log x := by field_simp
  have h3 := mul_le_mul_of_nonneg_left (two_rpow_neg_nZero_le hlx) hK
  have he : (20 * A + 10 * K_intTest) / Real.log x =
      20 * A / Real.log x + K_intTest * (10 / Real.log x) := by ring
  rw [he]
  linarith

/-- **Both words at one scale, at a rate.** -/
theorem scaleGood_prob_le_rate (u : List Bool) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in atTop, (winLaw x).expect
      (Set.indicator {N | ¬ ScaleGood u δ η x N} 1) ≤ C / Real.log x := by
  obtain ⟨C₁, hC₁, h₁⟩ := winGood_prob_le_rate u hδ hη
  obtain ⟨C₂, hC₂, h₂⟩ := winGood_prob_le_rate [true] (δ := 1 / 100) (by norm_num) hη
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  filter_upwards [h₁, h₂] with x hx1 hx2
  refine le_trans (prob_mono_support _ (B := {N | ¬ WinGood u δ (hgt η x) (lam x) N} ∪
    {N | ¬ WinGood [true] (1 / 100) (hgt η x) (lam x) N}) fun n _ hn => ?_)
    (le_trans (expect_indicator_union_le _ _ _) ?_)
  · simp only [ScaleGood, Set.mem_ofPred_eq, not_and_or] at hn
    exact hn
  · rw [add_div]
    linarith

/-! ## The chain at a rate -/

/-- **The chain distance at `x_j`**, by `dTV_chain_step`. -/
theorem dTV_chain_le {x : ℝ} (hx0 : 0 ≤ x) : ∀ j : ℕ,
    (∀ i ≤ j, 1 ≤ scale x i ∧ X_stab ≤ scale x i) →
    PMF.dTV ((winLaw x).map (passLoc ⌊scale x j⌋₊))
        ((winLaw (scale x j)).map (passLoc ⌊scale x j⌋₊)) ≤
      ∑ i ∈ Finset.range j, C_stab * Real.log (scale x (i + 1)) ^ (-c_stab)
  | 0, _ => by
    have : scale x 0 = x := by simp [scale]
    rw [this, dTV_self]
    simp
  | j + 1, h => by
    rw [Finset.sum_range_succ]
    have ih := dTV_chain_le hx0 j fun i hi => h i (by omega)
    have := dTV_chain_step j hx0 (h (j + 1) le_rfl).1 (h (j + 1) le_rfl).2
    linarith

/-- **One stage**: the location event at `x_j` fails with at most the probability of the start
event at `x_j`, plus the chain distance. -/
theorem stage_prob_le (u : List Bool) {δ η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 1000) :
    ∃ X₀ : ℝ, ∀ (x : ℝ) (j : ℕ), X₀ ≤ scale x j →
      (winLaw x).expect (Set.indicator
        {n | ¬ LocGood u δ η (scale x j) (passLoc ⌊scale x j⌋₊ n)} 1) ≤
        (winLaw (scale x j)).expect (Set.indicator {N | ¬ ScaleGood u δ η (scale x j) N} 1) +
        PMF.dTV ((winLaw x).map (passLoc ⌊scale x j⌋₊))
          ((winLaw (scale x j)).map (passLoc ⌊scale x j⌋₊)) := by
  obtain ⟨X₀, hX₀⟩ := locGoodPassLoc_holds u δ η hη hη1
  refine ⟨max X₀ X_windowBase, fun x j hx => ?_⟩
  set y := scale x j with hy
  have hloc : ((winLaw y).map (passLoc ⌊y⌋₊)).expect
      (Set.indicator {M | ¬ LocGood u δ η y M} 1) ≤
      (winLaw y).expect (Set.indicator {N | ¬ ScaleGood u δ η y N} 1) := by
    rw [expect_indicator_map]
    refine prob_mono_support _ fun n hn hbad => ?_
    obtain ⟨hodd, -, hhi⟩ := winLaw_support (le_trans (le_max_right _ _) hx) hn
    intro hsg
    exact hbad (hX₀ y (le_trans (le_max_left _ _) hx) n hodd hhi hsg)
  have hd := PMF.abs_expect_indicator_sub_le_dTV ((winLaw x).map (passLoc ⌊y⌋₊))
    ((winLaw y).map (passLoc ⌊y⌋₊)) {M | ¬ LocGood u δ η y M}
  have key : (winLaw x).expect ({n | ¬ LocGood u δ η y (passLoc ⌊y⌋₊ n)}.indicator 1) =
      ((winLaw x).map (passLoc ⌊y⌋₊)).expect ({M | ¬ LocGood u δ η y M}.indicator 1) :=
    (expect_indicator_map (winLaw x) (passLoc ⌊y⌋₊) {M | ¬ LocGood u δ η y M}).symm
  rw [key]
  linarith [(abs_le.mp hd).2]

/-- `∑_(i<n) r^i ≤ r^n / (r − 1)`. -/
theorem geom_sum_range_le {r : ℝ} (hr : 1 < r) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ r ^ n / (r - 1) := by
  rw [geom_sum_eq hr.ne']
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- `log(x_j)^(−κ) = (α^κ)^j log(x)^(−κ)`. -/
theorem log_scale_rpow {x : ℝ} (hx : 1 < x) (κ : ℝ) (j : ℕ) :
    Real.log (scale x j) ^ (-κ) = (alpha ^ κ) ^ j * Real.log x ^ (-κ) := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < alpha := by norm_num [alpha]
  rw [scale, Real.log_rpow hx0, Real.mul_rpow (pow_nonneg (inv_nonneg.mpr ha.le) _)
    (Real.log_nonneg hx.le), inv_pow, Real.inv_rpow (pow_nonneg ha.le _),
    Real.rpow_neg (pow_nonneg ha.le _), inv_inv, Real.rpow_pow_comm ha.le]

/-- The union bound over the start event and the `J` location events. -/
theorem chainFail_union_le {η : ℝ} (x : ℝ) (J : ℕ) :
    (winLaw x).expect (Set.indicator {n | ¬ (ScaleGood [true] (1 / 100) η x n ∧
      ∀ j < J, LocGood [true] (1 / 100) η (scale x j) (passLoc ⌊scale x j⌋₊ n))} 1) ≤
      (winLaw x).expect (Set.indicator {N | ¬ ScaleGood [true] (1 / 100) η x N} 1) +
        ∑ j ∈ Finset.range J, (winLaw x).expect (Set.indicator
          {n | ¬ LocGood [true] (1 / 100) η (scale x j) (passLoc ⌊scale x j⌋₊ n)} 1) := by
  refine le_trans (prob_mono_support _ (B := {N | ¬ ScaleGood [true] (1 / 100) η x N} ∪
    ⋃ j ∈ Finset.range J,
      {n | ¬ LocGood [true] (1 / 100) η (scale x j) (passLoc ⌊scale x j⌋₊ n)}) fun n _ hbad => ?_)
    (le_trans (expect_indicator_union_le _ _ _) (add_le_add le_rfl (prob_biUnion_le (winLaw x)
      (Finset.range J) fun j =>
        {n | ¬ LocGood [true] (1 / 100) η (scale x j) (passLoc ⌊scale x j⌋₊ n)})))
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, not_or,
    not_exists, not_not] at hcon
  exact hbad ⟨hcon.1, fun j hj => hcon.2 j hj⟩

/-- **The stage events at a rate** (`chainFail_prob_le`). -/
theorem chainFail_prob_le_holds {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 1000) :
    ∃ κ M X₀ : ℝ, 0 < κ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ (x : ℝ) (J : ℕ), (∀ j ≤ J, X ≤ scale x j) →
      (winLaw x).expect (Set.indicator {n | ¬ (ScaleGood [true] (1 / 100) η x n ∧
        ∀ j < J, LocGood [true] (1 / 100) η (scale x j) (passLoc ⌊scale x j⌋₊ n))} 1) ≤
        M * Real.log X ^ (-κ) := by
  set κ : ℝ := min c_stab 1 with hκdef
  have hκ : 0 < κ := lt_min c_stab_pos one_pos
  have hκ1 : κ ≤ 1 := min_le_right _ _
  have hκc : κ ≤ c_stab := min_le_left _ _
  set r : ℝ := alpha ^ κ with hrdef
  have hr : 1 < r := Real.one_lt_rpow (by norm_num [alpha]) hκ
  have hr1 : 0 < r - 1 := by linarith
  obtain ⟨C, hC, hrate⟩ := scaleGood_prob_le_rate [true] (δ := 1 / 100) (by norm_num) hη
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp hrate
  obtain ⟨X₂, hX₂⟩ := stage_prob_le [true] (δ := 1 / 100) hη hη1
  set G : ℝ := r / (r - 1) with hGdef
  have hG : 0 < G := div_pos (by linarith) hr1
  have hCs := C_stab_pos
  refine ⟨κ, (C + C_stab * G) * G, max (max X₁ X₂) (max X_stab (Real.exp 1)), hκ,
    fun X hX x J hJ => ?_⟩
  have hX1 : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXs : X_stab ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hXone : 1 ≤ X := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hXe
  have hlog1 : ∀ y, X ≤ y → 1 ≤ Real.log y := fun y hy => by
    have := Real.log_le_log (Real.exp_pos 1) (le_trans hXe hy)
    rwa [Real.log_exp] at this
  set ρ : ℝ → ℝ := fun y => Real.log y ^ (-κ) with hρdef
  have hρ0 : ∀ y, X ≤ y → 0 ≤ ρ y := fun y hy =>
    Real.rpow_nonneg (by linarith [hlog1 y hy]) _
  have hinv : ∀ y, X ≤ y → C / Real.log y ≤ C * ρ y := fun y hy => by
    have h1 := hlog1 y hy
    have : Real.log y ^ (-1 : ℝ) ≤ Real.log y ^ (-κ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    rw [Real.rpow_neg_one] at this
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left this hC
  have hstab : ∀ y, X ≤ y → C_stab * Real.log y ^ (-c_stab) ≤ C_stab * ρ y := fun y hy =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hlog1 y hy) (by linarith))
      hCs.le
  have hs0 : scale x 0 = x := by simp [scale]
  have hxX : X ≤ x := hs0 ▸ hJ 0 (Nat.zero_le _)
  have hx1 : 1 < x := lt_of_lt_of_le (lt_of_lt_of_le (by linarith [Real.add_one_le_exp 1]) hXe) hxX
  have hx0 : 0 ≤ x := by linarith
  have hρ : ∀ j, ρ (scale x j) = r ^ j * ρ x := fun j => log_scale_rpow hx1 κ j
  have hρx := hρ0 x hxX
  have hρJ : ρ (scale x J) ≤ ρ X :=
    Real.rpow_le_rpow_of_nonpos (by linarith [hlog1 X le_rfl])
      (Real.log_le_log hX0 (hJ J le_rfl)) (by linarith)
  -- the chain distance
  have hdTV : ∀ j ≤ J, PMF.dTV ((winLaw x).map (passLoc ⌊scale x j⌋₊))
      ((winLaw (scale x j)).map (passLoc ⌊scale x j⌋₊)) ≤ C_stab * G * ρ (scale x j) := by
    intro j hj
    refine le_trans (dTV_chain_le hx0 j fun i hi =>
      ⟨le_trans hXone (hJ i (by omega)), le_trans hXs (hJ i (by omega))⟩) ?_
    calc ∑ i ∈ Finset.range j, C_stab * Real.log (scale x (i + 1)) ^ (-c_stab)
        ≤ ∑ i ∈ Finset.range j, C_stab * ρ (scale x (i + 1)) :=
          Finset.sum_le_sum fun i hi => hstab _ (hJ (i + 1) (by simp at hi; omega))
      _ = C_stab * r * ρ x * ∑ i ∈ Finset.range j, r ^ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hρ, pow_succ]
          ring
      _ ≤ C_stab * r * ρ x * (r ^ j / (r - 1)) :=
          mul_le_mul_of_nonneg_left (geom_sum_range_le hr j) (by positivity)
      _ = C_stab * G * ρ (scale x j) := by
          rw [hρ, hGdef]
          field_simp
  -- each stage
  have hstage : ∀ j < J, (winLaw x).expect (Set.indicator
      {n | ¬ LocGood [true] (1 / 100) η (scale x j) (passLoc ⌊scale x j⌋₊ n)} 1) ≤
      (C + C_stab * G) * ρ (scale x j) := by
    intro j hj
    have h0 := hX₂ x j (le_trans hX2 (hJ j hj.le))
    have h1 := hX₁ (scale x j) (le_trans hX1 (hJ j hj.le))
    have h2 := hinv _ (hJ j hj.le)
    have h3 := hdTV j hj.le
    have he : (C + C_stab * G) * ρ (scale x j) = C * ρ (scale x j) + C_stab * G * ρ (scale x j) := by
      ring
    linarith
  -- the start
  have hstart : (winLaw x).expect (Set.indicator {N | ¬ ScaleGood [true] (1 / 100) η x N} 1) ≤
      C * ρ x := le_trans (hX₁ x (le_trans hX1 hxX)) (hinv x hxX)
  have hunion := chainFail_union_le (η := η) x J
  -- the geometric sum
  have hsumJ : ∑ j ∈ Finset.range J, ρ (scale x j) ≤ ρ (scale x J) / (r - 1) := by
    calc ∑ j ∈ Finset.range J, ρ (scale x j) = ρ x * ∑ j ∈ Finset.range J, r ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [hρ]; ring
      _ ≤ ρ x * (r ^ J / (r - 1)) := mul_le_mul_of_nonneg_left (geom_sum_range_le hr J) hρx
      _ = ρ (scale x J) / (r - 1) := by rw [hρ]; ring
  have hxJ : ρ x ≤ ρ (scale x J) := by
    rw [hρ]
    exact le_mul_of_one_le_left hρx (one_le_pow₀ hr.le)
  have hD : 0 ≤ C + C_stab * G := by positivity
  have hsum2 : ∑ j ∈ Finset.range J, (winLaw x).expect (Set.indicator
      {n | ¬ LocGood [true] (1 / 100) η (scale x j) (passLoc ⌊scale x j⌋₊ n)} 1) ≤
      (C + C_stab * G) * (ρ (scale x J) / (r - 1)) := by
    refine le_trans (Finset.sum_le_sum fun j hj => hstage j (Finset.mem_range.mp hj)) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsumJ hD
  have hGe : G = 1 + 1 / (r - 1) := by rw [hGdef]; field_simp; ring
  have hfin : C * ρ x + (C + C_stab * G) * (ρ (scale x J) / (r - 1)) ≤
      (C + C_stab * G) * G * ρ (scale x J) := by
    have h1 : C * ρ x ≤ (C + C_stab * G) * ρ (scale x J) :=
      mul_le_mul (by linarith [mul_pos hCs hG]) hxJ hρx hD
    have he : (C + C_stab * G) * G * ρ (scale x J) =
        (C + C_stab * G) * ρ (scale x J) + (C + C_stab * G) * (ρ (scale x J) / (r - 1)) := by
      rw [hGe]; ring
    linarith
  have hlast : (C + C_stab * G) * G * ρ (scale x J) ≤ (C + C_stab * G) * G * ρ X :=
    mul_le_mul_of_nonneg_left hρJ (by positivity)
  linarith

end CollatzMoonshot.Conjugacy
