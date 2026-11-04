/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawOrbit

/-!
# The orbit word law: one stage of descent

`stagePasses_holds` proves `StagePasses`.  Odd letters of an odd start sit exactly at its letter
times `valSum N j` (`exists_valSum_eq_of_odd`), so while the orbit stays above `w = ⌊z⌋` every
odd height is `> w`, and the height identity gives a descent of `0.18` per letter.  The next odd
height after the descent is the passage location, and the run of `0`s before it is capped by the
frequency of the letter `1` on the prefix of length `Λ`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-! ## Letter times -/

/-- Each Syracuse step of an odd start takes at least one letter. -/
theorem valSum_succ_ge {N : ℕ} (hN : N % 2 = 1) (k : ℕ) : valSum N k + 1 ≤ valSum N (k + 1) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := syr_iterate_odd N k hN
  have hv : 1 ≤ padicValNat 2 (3 * syr^[k] N + 1) :=
    one_le_padicValNat_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero (by omega))
  rw [valSum_succ]
  omega

/-- Letter times are strictly increasing. -/
theorem valSum_lt {N : ℕ} (hN : N % 2 = 1) {j j' : ℕ} (h : j < j') : valSum N j < valSum N j' :=
  lt_of_lt_of_le (Nat.lt_of_succ_le (valSum_succ_ge hN j)) (valSum_mono N h)

/-- The `k`-th letter time is at least `k`. -/
theorem le_valSum {N : ℕ} (hN : N % 2 = 1) (k : ℕ) : k ≤ valSum N k := by
  induction k with
  | zero => simp
  | succ k ih => exact le_trans (Nat.succ_le_succ ih) (valSum_succ_ge hN k)

/-- Every positive time lies in a bracket `(valSum N k, valSum N (k + 1)]`. -/
theorem exists_valSum_bracket {N : ℕ} (hN : N % 2 = 1) {t : ℕ} (ht : 0 < t) :
    ∃ k, valSum N k < t ∧ t ≤ valSum N (k + 1) := by
  classical
  have hex : ∃ j, t ≤ valSum N j := ⟨t, le_valSum hN t⟩
  set K := Nat.find hex with hK
  have hKspec : t ≤ valSum N K := Nat.find_spec hex
  have hK0 : K ≠ 0 := by
    intro h0
    rw [h0, valSum_zero] at hKspec
    omega
  obtain ⟨k, hk⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  refine ⟨k, ?_, hk ▸ hKspec⟩
  have := Nat.find_min hex (show k < K by omega)
  omega

/-- **Odd letters are at letter times.**  For odd `N`, an odd height `tstep^[i] N` is a Syracuse
iterate: `i = valSum N j` for some `j`. -/
theorem exists_valSum_eq_of_odd {N : ℕ} (hN : N % 2 = 1) {i : ℕ} (hi : tstep^[i] N % 2 = 1) :
    ∃ j, valSum N j = i := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨k, hk1, hk2⟩ := exists_valSum_bracket hN hpos
  rcases Nat.lt_or_ge i (valSum N (k + 1)) with hlt | hge
  · have := (tstep_between hN hk1 hk2).2 i le_rfl hlt
    simp [accWord, hi] at this
  · exact ⟨k + 1, by omega⟩

/-- The letter time of a passage is at most that of any Syracuse time below the threshold. -/
theorem ltime_le_of_le {w N j : ℕ} (hj : syr^[j] N ≤ w) : ltime w N ≤ valSum N j :=
  valSum_mono N (Nat.sInf_le hj)

/-! ## Counting letters -/

/-- A prefix good for the letter `1` brackets the odd count. -/
theorem abs_oddCount_sub_le {δ : ℝ} {H Λ M ℓ : ℕ} (h : PrefGood [true] δ H Λ M) (hH : H ≤ ℓ)
    (hΛ : ℓ ≤ Λ) : |(oddCount M ℓ : ℝ) - ℓ / 2| ≤ δ * ℓ := by
  have := h ℓ hH hΛ
  rw [wdev, wcnt_true_eq_oddCount] at this
  convert this using 3
  simp
  ring

/-- Over a run of `0` letters the odd count stays put. -/
theorem oddCount_eq_of_false {M a : ℕ} : ∀ d : ℕ, (∀ i, a ≤ i → i < a + d → accWord M i = false) →
    oddCount M (a + d) = oddCount M a
  | 0, _ => rfl
  | d + 1, h => by
    rw [← add_assoc, oddCount_succ', oddCount_eq_of_false d fun i h1 h2 => h i h1 (by omega)]
    have := h (a + d) (by omega) (by omega)
    simp only [accWord, decide_eq_false_iff_not] at this
    rw [if_neg this, add_zero]

/-- The height correction is at most `t / w` while every odd height before `t` is `≥ w`. -/
theorem heightCorr_le_of_ge {M t w : ℕ} (hw : 1 ≤ w)
    (h : ∀ i < t, tstep^[i] M % 2 = 1 → w ≤ tstep^[i] M) : heightCorr M t ≤ t / w := by
  unfold heightCorr
  have hb : ∀ i ∈ (Finset.range t).filter (fun i => tstep^[i] M % 2 = 1),
      Real.logb 2 (1 + 1 / (3 * (tstep^[i] M : ℝ))) ≤ 1 / (w : ℝ) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact logb_corr_le_inv hw (h i hi.1 hi.2)
  refine le_trans (Finset.sum_le_sum hb) ?_
  rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_one_div (t : ℝ)]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have := Finset.card_filter_le (Finset.range t) (fun i => tstep^[i] M % 2 = 1)
  rw [Finset.card_range] at this
  exact_mod_cast this

/-! ## One stage -/

/-- **One stage of descent** (`StagePasses`). -/
theorem stagePasses_holds : StagePasses := by
  intro M H Λ y z hM hMy hz2 hzy hΛ hΛz hpref
  set w := ⌊z⌋₊ with hwdef
  have hz0 : 0 < z := by linarith
  have hw2 : 2 ≤ w := Nat.le_floor (by exact_mod_cast hz2)
  have hwz : (w : ℝ) ≤ z := Nat.floor_le hz0.le
  have hzw : z < w + 1 := Nat.lt_floor_add_one z
  have hw2R : (2 : ℝ) ≤ w := by exact_mod_cast hw2
  have hM1 : 1 ≤ M := by omega
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  -- the drop `D ≥ 0` and the length `Λ ≥ 48`
  have hD : 0 ≤ Real.logb 2 y - Real.logb 2 z := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hz0 hzy
    linarith
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hΛ48 : (40 : ℝ) ≤ Λ := by nlinarith
  -- the probe time `t₀ = ⌊9 Λ / 10⌋`
  set t₀ := 9 * Λ / 10 with ht₀def
  have ht₀a : 9 * Λ ≤ 10 * t₀ + 9 := by omega
  have ht₀b : 10 * t₀ ≤ 9 * Λ := by omega
  have ht₀aR : 9 * (Λ : ℝ) ≤ 10 * t₀ + 9 := by exact_mod_cast ht₀a
  have ht₀bR : 10 * (t₀ : ℝ) ≤ 9 * Λ := by exact_mod_cast ht₀b
  have hHt₀ : H ≤ t₀ := by
    have : (H : ℝ) ≤ t₀ := by linarith
    exact_mod_cast this
  have ht₀Λ : t₀ ≤ Λ := by omega
  have ht₀pos : 0 < t₀ := by
    have : (0 : ℝ) < t₀ := by linarith
    exact_mod_cast this
  -- odd counts at `t₀` and at `Λ`
  have ho₀ := abs_oddCount_sub_le hpref hHt₀ ht₀Λ
  have hoΛ := abs_oddCount_sub_le hpref (le_trans hHt₀ ht₀Λ) le_rfl
  rw [abs_le] at ho₀ hoΛ
  obtain ⟨k, hk1, hk2⟩ := exists_valSum_bracket hM ht₀pos
  by_cases hA : ∃ j ≤ k, syr^[j] M ≤ w
  · -- passed before the probe time
    obtain ⟨j, hjk, hj⟩ := hA
    refine ⟨⟨j, hj⟩, ?_⟩
    have := le_trans (ltime_le_of_le hj) (valSum_mono M hjk)
    omega
  · push Not at hA
    -- every odd height before `t₀` is above `w`
    have hodd : ∀ i < t₀, tstep^[i] M % 2 = 1 → w ≤ tstep^[i] M := by
      intro i hi hio
      obtain ⟨j, hj⟩ := exists_valSum_eq_of_odd hM hio
      have hjk : j ≤ k := by
        by_contra hjk
        have := valSum_mono M (show k + 1 ≤ j by omega)
        omega
      rw [← hj, ← syr_iterate_eq_tstep hM]
      exact (hA j hjk).le
    have hcorr := heightCorr_le_of_ge (by omega) hodd
    have ht₀w : (t₀ : ℝ) ≤ w := by
      have : t₀ ≤ w := by
        have : (t₀ : ℝ) < w + 1 := by
          have : (t₀ : ℝ) ≤ Λ := by exact_mod_cast ht₀Λ
          linarith
        exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
      exact_mod_cast this
    have hcorr1 : heightCorr M t₀ ≤ 1 := by
      refine le_trans hcorr ?_
      rw [div_le_one (by linarith)]
      exact ht₀w
    -- the height at the probe time is below `w`
    have hT1 := one_le_tstep_iterate hM1 t₀
    have hT1R : (1 : ℝ) ≤ tstep^[t₀] M := by exact_mod_cast hT1
    have hid := height_identity hM1 t₀
    have hl3 := logb_three_lt
    have hl3' : 0 < Real.logb 2 3 := by linarith [one_le_logb_three]
    have hMyl : Real.logb 2 M ≤ Real.logb 2 y :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hMy
    have hwl : Real.logb 2 z - 1 ≤ Real.logb 2 w := by
      have h1 : z / 2 ≤ w := by linarith
      have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) h1
      rw [Real.logb_div (by linarith) (by norm_num), Real.logb_self_eq_one (by norm_num)] at h2
      exact h2
    have hoR : (oddCount M t₀ : ℝ) * Real.logb 2 3 ≤ (51 / 100 * t₀) * (8 / 5) := by
      have h0 : (0 : ℝ) ≤ oddCount M t₀ := Nat.cast_nonneg _
      have h1 : (oddCount M t₀ : ℝ) ≤ 51 / 100 * t₀ := by linarith
      calc (oddCount M t₀ : ℝ) * Real.logb 2 3 ≤ (51 / 100 * t₀) * Real.logb 2 3 :=
            mul_le_mul_of_nonneg_right h1 hl3'.le
        _ ≤ (51 / 100 * t₀) * (8 / 5) :=
            mul_le_mul_of_nonneg_left hl3.le (by positivity)
    have hlt : Real.logb 2 (tstep^[t₀] M) < Real.logb 2 w := by
      rw [hid]
      nlinarith
    have hTw : tstep^[t₀] M < w := by
      have := (Real.logb_lt_logb_iff (b := 2) (by norm_num) (by linarith) (by linarith)).mp hlt
      exact_mod_cast this
    obtain ⟨hsyr, hzero⟩ := tstep_between hM hk1 hk2
    have hpass : syr^[k + 1] M ≤ w := by omega
    refine ⟨⟨k + 1, hpass⟩, le_trans (ltime_le_of_le hpass) ?_⟩
    -- the run of `0`s after the probe time is short
    by_contra hlong
    push Not at hlong
    have hrun := oddCount_eq_of_false (M := M) (a := t₀) (Λ - t₀)
      fun i h1 h2 => hzero i h1 (by omega)
    rw [Nat.add_sub_cancel' ht₀Λ] at hrun
    have hrunR : (oddCount M Λ : ℝ) = oddCount M t₀ := by exact_mod_cast hrun
    nlinarith

end CollatzMoonshot.Conjugacy

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-! ## Scale bookkeeping -/

/-- `log₂ (x^r) = r log₂ x`. -/
theorem logb_rpow_eq {x : ℝ} (hx : 0 < x) (r : ℝ) : Real.logb 2 (x ^ r) = r * Real.logb 2 x := by
  unfold Real.logb
  rw [Real.log_rpow hx]
  ring

/-- The window cap is at least `log₂ x / 20 − 1`. -/
theorem lam_ge (x : ℝ) : Real.logb 2 x / 20 - 1 ≤ lam x := by
  unfold lam
  rcases le_or_gt 0 (Real.logb 2 x / 20) with h | h
  · exact (Nat.sub_one_lt_floor _).le
  · linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌊Real.logb 2 x / 20⌋₊)]

/-- The window cap is at most `log₂ x / 20`, for `x ≥ 1`. -/
theorem lam_le {x : ℝ} (hx : 1 ≤ x) : (lam x : ℝ) ≤ Real.logb 2 x / 20 :=
  Nat.floor_le (div_nonneg (Real.logb_nonneg (by norm_num) hx) (by norm_num))

/-- The shortest window is at most `η log₂ x + 1`. -/
theorem hgt_le {η x : ℝ} (h : 0 ≤ η * Real.logb 2 x) : (hgt η x : ℝ) ≤ η * Real.logb 2 x + 1 :=
  (Nat.ceil_lt_add_one h).le

/-- `log₂ x ≤ 2 x`. -/
theorem logb_le_two_mul {x : ℝ} (hx : 0 < x) : Real.logb 2 x ≤ 2 * x := by
  have h1 := Real.log_le_sub_one_of_pos hx
  have h2 : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  unfold Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The window cap is at most `x`, for `x ≥ 1`. -/
theorem lam_le_self {x : ℝ} (hx : 1 ≤ x) : (lam x : ℝ) ≤ x := by
  have := lam_le hx
  have := logb_le_two_mul (by linarith : (0 : ℝ) < x)
  linarith

/-- `log₂ x ≥ n` from `x ≥ 2^n`. -/
theorem le_logb_of_two_pow_le {x : ℝ} {n : ℕ} (hx : (2 : ℝ) ^ n ≤ x) : (n : ℝ) ≤ Real.logb 2 x := by
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hx
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this

/-! ## The location event -/

/-- **The location event from the start event** (`LocGoodPassLoc`): the start's windows reach past
its passage below `x`, since one stage takes at most `lam x` letters. -/
theorem locGoodPassLoc_holds : LocGoodPassLoc := by
  intro u δ η hη hη1
  refine ⟨2 ^ (10000 : ℕ), fun x hx N hN hNx hsg => ?_⟩
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_self_pow₀ (by norm_num) (by norm_num)) hx
  have hx0 : 0 < x := lt_of_lt_of_le two_pos hx2
  have hL := le_logb_of_two_pow_le hx
  push_cast at hL
  clear hx
  have hy := logb_rpow_eq hx0 (alpha ^ 2)
  have hxy : x ≤ x ^ alpha ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (x := x) (by linarith)
      (show (1 : ℝ) ≤ alpha ^ 2 by norm_num [alpha])
    simpa using this
  have hlam := lam_ge x
  have hhgt := hgt_le (η := η) (x := x) (by positivity)
  have hcov : 20 * (Real.logb 2 (x ^ alpha ^ 2) - Real.logb 2 x + 2) + 4 * (hgt η x : ℝ) ≤
      lam x := by
    rw [hy]
    have ha : alpha ^ 2 = 1.002001 := by norm_num [alpha]
    rw [ha]
    have hηL : η * Real.logb 2 x ≤ Real.logb 2 x / 1000 := by nlinarith
    linarith
  have hpref : PrefGood [true] (1 / 100) (hgt η x) (lam x) N := by
    have := prefGood_of_winGood (b := 0) hsg.2 (Nat.zero_le _)
    rwa [Function.iterate_zero_apply] at this
  obtain ⟨hp, hlt⟩ := stagePasses_holds N _ _ (x ^ alpha ^ 2) x hN hNx hx2 hxy hcov
    (lam_le_self (by linarith)) hpref
  rw [passLoc_eq_tstep hN hp]
  exact ⟨prefGood_of_winGood hsg.1 hlt, prefGood_of_winGood hsg.2 hlt⟩

end CollatzMoonshot.Conjugacy
