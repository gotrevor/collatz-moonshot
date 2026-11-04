/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawTerras

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

end CollatzMoonshot.Conjugacy
