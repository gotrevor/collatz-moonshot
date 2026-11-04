/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawDensity

/-!
# The orbit word law: windows give density

`logDens0OfWindow_holds` proves `LogDens0OfWindow`.  The windows `[y_k^α, y_k^(α²)]` with
`y_k = x₀^(α^k)` tile `[x₀^α, ∞)`, since `y_k^(α²) = y_(k+1)^α`.  The log-weight of `B` in window
`k` is the window mass times the `winLaw y_k`-probability of `B` (`sum_window_le`), and the mass is at
most four times the log-length `w_k = (α − 1) α^(k+1) log x₀` of the window (`windowMass_le`).  The
log-lengths of the windows below `X` sum to at most `α log X`, so a probability tending to `0` gives
log-weight `o(log X)`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-! ## One window -/

/-- **The log-weight of `B` in one window** is at most the window mass times the probability. -/
theorem sum_window_le (B : ℕ → Prop) [DecidablePred B] {x : ℝ} (hx : X_windowBase ≤ x) :
    ∑ n ∈ (logWindow (x ^ alpha) (x ^ alpha ^ 2)).filter B, (1 : ℝ) / n ≤
      windowMass (x ^ alpha) (x ^ alpha ^ 2) * (winLaw x).expect (Set.indicator {n | B n} 1) := by
  have hx0 : 0 ≤ x := le_trans (by unfold X_windowBase X_nZeroPos; positivity) hx
  have hpow : (x ^ alpha) ^ alpha = x ^ alpha ^ 2 := by rw [← Real.rpow_mul hx0, pow_two]
  have hne := logWindow_nonempty_atX x hx (x ^ alpha) (Set.mem_insert _ _)
  rw [hpow] at hne
  set W := logWindow (x ^ alpha) (x ^ alpha ^ 2) with hWdef
  set D := windowMass (x ^ alpha) (x ^ alpha ^ 2) with hDdef
  have hW0 : ∀ n ∈ W, n ≠ 0 := by
    intro n hn
    simp only [hWdef, logWindow, Finset.mem_filter] at hn
    omega
  have hD : 0 < D := by
    rw [hDdef, windowMass]
    refine Finset.sum_pos (fun n hn => ?_) hne
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (hW0 n hn)
    positivity
  have happ : ∀ n ∈ W, ((winLaw x) n).toReal = (1 / n) / D := by
    intro n hn
    rw [winLaw, logUnifOdd_apply_of_nonempty hne, if_pos hn, ENNReal.toReal_div,
      ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_sum fun M hM => by
        rw [ne_eq, ENNReal.inv_eq_top, Nat.cast_eq_zero]
        exact hW0 M hM]
    rw [hDdef, windowMass, one_div]
    congr 1
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  calc ∑ n ∈ W.filter B, (1 : ℝ) / n
      = D * ∑ n ∈ W.filter B, ((winLaw x) n).toReal * Set.indicator {n | B n} 1 n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.mem_filter] at hn
        rw [happ n hn.1, Set.indicator_of_mem (show n ∈ {n | B n} from hn.2)]
        simp only [Pi.one_apply, mul_one]
        field_simp
    _ ≤ D * (winLaw x).expect (Set.indicator {n | B n} 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hD.le
        exact Summable.sum_le_tsum _ (fun n _ => mul_nonneg ENNReal.toReal_nonneg
          (Set.indicator_nonneg (fun _ _ => zero_le_one) n)) (summable_indicator_term _ _)

/-- The window mass is at most `(α − 1) α log x / 2 + 3`, by Tao's (5.19). -/
theorem windowMass_le {x : ℝ} (hx : X_windowBase ≤ x) :
    windowMass (x ^ alpha) (x ^ alpha ^ 2) ≤ (alpha - 1) / 2 * (alpha * Real.log x) + 3 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by unfold X_windowBase X_nZeroPos; positivity) hx
  have hpow : (x ^ alpha) ^ alpha = x ^ alpha ^ 2 := by rw [← Real.rpow_mul hx0.le, pow_two]
  have h := windowMass_estimate_atCX x hx (x ^ alpha) (Set.mem_insert _ _)
  rw [hpow, Real.log_rpow hx0] at h
  linarith [(abs_le.mp h).2]

/-! ## Sums over a cover -/

/-- A sum over a union of finsets is at most the sum of the sums, for nonnegative terms. -/
theorem sum_biUnion_le_of_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Finset ℕ)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∑ n ∈ s.biUnion t, f n ≤ ∑ k ∈ s, ∑ n ∈ t k, f n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hk]
    have h := Finset.sum_union_inter (s₁ := t k) (s₂ := s.biUnion t) (f := f)
    have h0 : 0 ≤ ∑ n ∈ t k ∩ s.biUnion t, f n := Finset.sum_nonneg fun n _ => hf n
    linarith

/-- The log-lengths `(α − 1) α^(k+1) ℓ` telescope: their sum below `m` is `(α^(m+1) − α) ℓ`. -/
theorem sum_logLength (ℓ : ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, (alpha - 1) * alpha ^ (k + 1) * ℓ = (alpha ^ (m + 1) - alpha) * ℓ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- `log X_windowBase ≥ 1000`. -/
theorem log_windowBase_ge : 1000 ≤ Real.log X_windowBase := by
  have h1 : Real.log ((2 : ℝ) ^ (2000 : ℝ)) ≤ Real.log X_windowBase :=
    Real.log_le_log (by positivity) (le_max_right _ _)
  rw [Real.log_rpow (by norm_num)] at h1
  linarith [Real.log_two_gt_d9]

/-! ## Windows give density -/

/-- **Windows give density** (`LogDens0OfWindow`). -/
theorem logDens0OfWindow_holds : LogDens0OfWindow := by
  classical
  intro B hB
  set x₀ : ℝ := X_windowBase with hx₀def
  have hℓ : 1000 ≤ Real.log x₀ := log_windowBase_ge
  have hx₀pos : 0 < x₀ := lt_of_lt_of_le (show (0 : ℝ) < X_nZeroPos by
    unfold X_nZeroPos; positivity) (le_max_left _ _)
  have hx₀1 : 1 < x₀ := by
    by_contra h
    push Not at h
    have := Real.log_nonpos hx₀pos.le h
    linarith
  set ℓ : ℝ := Real.log x₀ with hℓdef
  set y : ℕ → ℝ := fun k => x₀ ^ (alpha ^ k) with hydef
  have hα1 : 1 ≤ alpha := by norm_num [alpha]
  have hy1 : ∀ k, x₀ ≤ y k := fun k => by
    simpa using Real.rpow_le_rpow_of_exponent_le hx₀1.le (one_le_pow₀ hα1 : 1 ≤ alpha ^ k)
  have hy0 : ∀ k, 0 < y k := fun k => lt_of_lt_of_le (by linarith) (hy1 k)
  have hyα : ∀ k, y k ^ alpha = x₀ ^ (alpha ^ (k + 1)) := fun k => by
    simp only [hydef]
    rw [← Real.rpow_mul (by linarith), pow_succ]
  have hyα2 : ∀ k, y k ^ alpha ^ 2 = y (k + 1) ^ alpha := fun k => by
    rw [hyα]
    simp only [hydef]
    rw [← Real.rpow_mul (by linarith)]
    congr 1
    ring
  have hmono : ∀ k k', k ≤ k' → y k ^ alpha ≤ y k' ^ alpha := fun k k' h => by
    rw [hyα, hyα]
    exact Real.rpow_le_rpow_of_exponent_le hx₀1.le (pow_le_pow_right₀ hα1 (by omega))
  have hytend : Tendsto y atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => alpha ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num [alpha])
    exact (tendsto_rpow_atTop_of_base_gt_one x₀ hx₀1).comp h1
  have htend : Tendsto (fun k => y k ^ alpha) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) hytend
    have := Real.rpow_le_rpow_of_exponent_le (le_trans hx₀1.le (hy1 k)) hα1
    simpa using this
  have hex : ∀ t : ℝ, ∃ m, t ≤ y m ^ alpha := fun t => (htend.eventually_ge_atTop t).exists
  -- probabilities along the windows
  set P : ℕ → ℝ := fun k => (winLaw (y k)).expect (Set.indicator {n | B n} 1) with hPdef
  have hP0 : ∀ k, 0 ≤ P k := fun k => prob_nonneg _ _
  have hPt : Tendsto P atTop (𝓝 0) := hB.comp hytend
  -- one window
  set w : ℕ → ℝ := fun k => (alpha - 1) * alpha ^ (k + 1) * ℓ with hwdef
  have hw1 : ∀ k, 1 ≤ w k := fun k => by
    have h1 : 1 ≤ alpha ^ (k + 1) := one_le_pow₀ hα1
    have h2 : (1 : ℝ) ≤ (alpha - 1) * ℓ := by
      have : alpha - 1 = 1 / 1000 := by norm_num [alpha]
      rw [this]
      linarith
    simp only [hwdef]
    nlinarith
  have hwin : ∀ k, ∑ n ∈ (logWindow (y k ^ alpha) (y k ^ alpha ^ 2)).filter B, (1 : ℝ) / n ≤
      4 * w k * P k := by
    intro k
    have hxk : X_windowBase ≤ y k := hy1 k
    refine le_trans (sum_window_le B hxk) (mul_le_mul_of_nonneg_right ?_ (hP0 k))
    refine le_trans (windowMass_le hxk) ?_
    rw [show Real.log (y k) = alpha ^ k * ℓ by
      simp only [hydef]
      rw [Real.log_rpow (by linarith)]]
    have := hw1 k
    have he : (alpha - 1) / 2 * (alpha * (alpha ^ k * ℓ)) = w k / 2 := by
      simp only [hwdef]
      ring
    rw [he]
    linarith
  -- the cover
  have hcover : ∀ X : ℕ,
      ∑ n ∈ (Finset.Ico 1 X).filter (fun n => n % 2 = 1 ∧ B n), (1 : ℝ) / n ≤
        ∑ n ∈ Finset.range ⌈y 0 ^ alpha⌉₊, (1 : ℝ) / n +
          ∑ k ∈ Finset.range (Nat.find (hex X)), 4 * w k * P k := by
    intro X
    set F := (Finset.Ico 1 X).filter (fun n => n % 2 = 1 ∧ B n) with hF
    rw [← Finset.sum_filter_add_sum_filter_not F (fun n => (n : ℝ) < y 0 ^ alpha)]
    refine add_le_add ?_ ?_
    · refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => by positivity
      rw [Finset.mem_filter] at hn
      exact Finset.mem_range.mpr (Nat.lt_ceil.mpr hn.2)
    · set m := Nat.find (hex X) with hm
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := (Finset.range m).biUnion
        fun k => (logWindow (y k ^ alpha) (y k ^ alpha ^ 2)).filter B) (fun n hn => ?_)
        fun n _ _ => by positivity) (le_trans (sum_biUnion_le_of_nonneg _ _ _
          fun n => by positivity) (Finset.sum_le_sum fun k _ => hwin k))
      simp only [hF, Finset.mem_filter, Finset.mem_Ico, not_lt] at hn
      obtain ⟨⟨⟨_, hnX⟩, hodd, hB'⟩, hlo⟩ := hn
      have hk : ∃ k, (n : ℝ) ≤ y k ^ alpha ^ 2 := by
        obtain ⟨j, hj⟩ := hex n
        exact ⟨j, le_trans hj (by rw [hyα2]; exact hmono _ _ (by omega))⟩
      set k := Nat.find hk with hkdef
      have hk1 : (n : ℝ) ≤ y k ^ alpha ^ 2 := Nat.find_spec hk
      have hk2 : y k ^ alpha ≤ n := by
        rcases Nat.eq_zero_or_eq_succ_pred k with h0 | hs
        · rw [h0]
          exact hlo
        · have := Nat.find_min hk (show k.pred < k by omega)
          push Not at this
          rw [hs, ← hyα2]
          exact this.le
      have hkm : k < m := by
        by_contra hcon
        push Not at hcon
        have h1 : (X : ℝ) ≤ y m ^ alpha := Nat.find_spec (hex X)
        have h2 := hmono m k hcon
        have h3 : (n : ℝ) < X := by exact_mod_cast hnX
        linarith
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, logWindow]
      refine ⟨k, hkm, ⟨?_, hodd, hk2, hk1⟩, hB'⟩
      exact Nat.lt_succ_of_le (by exact_mod_cast hk1.trans (Nat.le_ceil _))
  -- the windows below `X` have total log-length at most `α log X`
  have hgeom : ∀ X : ℕ, ∑ k ∈ Finset.range (Nat.find (hex X)), w k ≤ alpha * Real.log X := by
    intro X
    have hlX : 0 ≤ Real.log X := Real.log_natCast_nonneg X
    have hα0 : (0 : ℝ) ≤ alpha := by norm_num [alpha]
    simp only [hwdef]
    rw [sum_logLength]
    rcases hj : Nat.find (hex X) with _ | j
    · simp only [zero_add, pow_one, sub_self, zero_mul]
      positivity
    · have hmin := Nat.find_min (hex X) (show j < Nat.find (hex X) by omega)
      push Not at hmin
      have hlog := Real.log_lt_log (by rw [hyα]; positivity) hmin
      rw [hyα, Real.log_rpow (by linarith)] at hlog
      rw [pow_succ]
      have hℓ0 : 0 ≤ ℓ := by linarith
      have : 0 ≤ alpha * ℓ := by positivity
      nlinarith
  rw [LogDens0, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hPt.eventually (ge_mem_nhds
    (show (0 : ℝ) < ε / 16 by positivity)))
  set C : ℝ := ∑ n ∈ Finset.range ⌈y 0 ^ alpha⌉₊, (1 : ℝ) / n +
    ∑ k ∈ Finset.range k₀, 4 * w k * P k with hC
  have hClim : Tendsto (fun X : ℕ => C / Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hClim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with X hXC hXlog
  simp only [Function.comp_apply] at hXlog
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (logWeight_nonneg _ X)]
  set m := Nat.find (hex X) with hm
  have hsplit : ∑ k ∈ Finset.range m, 4 * w k * P k ≤
      ∑ k ∈ Finset.range k₀, 4 * w k * P k + ε / 4 * ∑ k ∈ Finset.range m, w k := by
    have hterm : ∀ k ∈ Finset.range m, 4 * w k * P k ≤
        (if k < k₀ then 4 * w k * P k else 0) + ε / 4 * w k := by
      intro k _
      have hw0 : 0 ≤ w k := le_trans zero_le_one (hw1 k)
      split_ifs with hk
      · have : 0 ≤ ε / 4 * w k := by positivity
        linarith
      · have := hk₀ k (by omega)
        nlinarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
    refine add_le_add ?_ le_rfl
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => ?_
    · simp only [Finset.mem_filter] at hk
      exact Finset.mem_range.mpr hk.2
    · have := hP0 k
      have := hw1 k
      positivity
  have hbound := hcover X
  have hg := hgeom X
  have hα2 : alpha ≤ 2 := by norm_num [alpha]
  rw [div_lt_iff₀ hXlog]
  rw [div_lt_iff₀ hXlog] at hXC
  have hsum : ∑ n ∈ (Finset.Ico 1 X).filter (fun n => n % 2 = 1 ∧ B n), (1 : ℝ) / n ≤
      C + ε / 4 * (alpha * Real.log X) := by
    have : ε / 4 * ∑ k ∈ Finset.range m, w k ≤ ε / 4 * (alpha * Real.log X) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    rw [hC]
    linarith
  have h2 : ε / 4 * (alpha * Real.log X) ≤ ε / 2 * Real.log X := by
    have : 0 ≤ ε / 4 * Real.log X := by positivity
    nlinarith
  calc _ = ∑ n ∈ (Finset.Ico 1 X).filter (fun n => n % 2 = 1 ∧ B n), (1 : ℝ) / n := by
          congr
    _ ≤ C + ε / 4 * (alpha * Real.log X) := hsum
    _ < ε * Real.log X := by linarith

end CollatzMoonshot.Conjugacy
