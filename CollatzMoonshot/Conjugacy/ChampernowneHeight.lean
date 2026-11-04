/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.ChampernowneAveraged

/-!
# Single-letter balance is a law for the height of an orbit

The parity letters of `n` and its height are tied by an exact identity (`height_identity`):
`log₂ T^t n = log₂ n − t + O log₂ 3 + heightCorr n t`, with `O` the odd letters and `heightCorr` a correction
that is small while the orbit is high.  So over any initial segment of stage `k`
(`abs_sum_height_sub_le`), up to `O(2^k)`,

  `∑ log₂ T^(Ck) n − m (1 − C β) k = log₂ 3 · X + ∑ heightCorr`,

with `β = 1 − log₂ 3 / 2 = 1 / C*` and `X` the signed single-letter errors over the offsets `≥ k`, the
single-letter case of `AveragedMixing`.

* While `heightCorr` is negligible (`LowHeightNegligible`), the single-letter case is exactly
  `MeanHeightLaw C`, that the mean height at time `C k` is `(1 − C / C*) k + o(k)`
  (`singleLetterAveraged_iff_meanHeightLaw`).
* Normality supplies `LowHeightNegligible` (`lowHeightNegligible_of_normal`): a visit to a fixed `y`
  starts a fixed word, namely the first `L` letters of `y`, whose frequency is `2^(−L)`.  So a normal
  `𝒞_C` obeys the law (`meanHeightLaw_of_normal`).
* For `C ≥ 5` the law predicts a negative height, so it fails (`not_meanHeightLaw_of_five_le`).  That is
  the teeth of the statement, and the height side of `not_normal_of_five_le`.

`experiments/conjugacy/mean_height.py` checks the identity on sampled orbits and compares the law with
data out to `k = 400`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- The correction to `O log₂ 3` in the height of `n` at time `t`: `∑ log₂ (1 + 1 / (3 y))` over the
odd heights `y` among the first `t` steps. -/
noncomputable def heightCorr (n t : ℕ) : ℝ :=
  ∑ i ∈ (Finset.range t).filter (fun i => tstep^[i] n % 2 = 1),
    Real.logb 2 (1 + 1 / (3 * (tstep^[i] n : ℝ)))

/-- The predicted height at time `C k`, per unit of `k`: `1 − C / C*`. -/
noncomputable def heightRate (C : ℕ) : ℝ := 1 - C * (1 - Real.logb 2 3 / 2)

/-- The signed single-letter errors over the offsets `≥ k`, on the first `m` integers of stage `k`. -/
noncomputable def letterExcess (C k m : ℕ) : ℝ :=
  ∑ t ∈ (Finset.range (C * k)).filter (fun t => k ≤ t ∧ t + [true].length ≤ C * k),
    stageError (fun s => [true].getD s false) [true].length k t m

/-- The single-letter case of `AveragedMixing`. -/
def SingleLetterAveraged (C : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ m : ℕ, m ≤ 2 ^ (k - 1) →
    |letterExcess C k m| ≤ δ * k * 2 ^ (k - 1)

/-- **Node: the mean height law.**  Over every initial segment of stage `k`, the mean of
`log₂ T^(Ck) n` is `(1 − C / C*) k`, up to `δ k 2^(k-1)` in total.  False for `C ≥ 5`
(`not_meanHeightLaw_of_five_le`); for `C ≤ 4` a normal `𝒞_C` obeys it (`meanHeightLaw_of_normal`).
Confidence 75% for `C ≤ 4`. -/
def MeanHeightLaw (C : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ m : ℕ, m ≤ 2 ^ (k - 1) →
    |∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), Real.logb 2 (tstep^[C * k] n) -
        m * (heightRate C * k)| ≤ δ * k * 2 ^ (k - 1)

/-- **Node.**  Over stage `k`, the correction is `o(k)` per start: orbits spend a vanishing fraction of
their first `C k` steps at bounded height.  For `C ≥ 5` it fails under single-letter balance. -/
def LowHeightNegligible (C : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), heightCorr n (C * k) ≤ δ * k * 2 ^ (k - 1)

/-- `log₂ 3 < 8/5`, from the threshold bound. -/
theorem logb_three_lt : Real.logb 2 3 < 8 / 5 := by
  obtain ⟨h4, h5⟩ := threshold_bounds
  have hpos : 0 < 2 - Real.logb 2 3 := by
    by_contra hn
    have := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2) (not_lt.mp hn)
    linarith
  rw [div_lt_iff₀ hpos] at h5
  linarith

/-- `1 ≤ log₂ 3`. -/
theorem one_le_logb_three : 1 ≤ Real.logb 2 3 := by
  have := Real.logb_le_logb_of_le (b := 2) (x := 2) (y := 3) (by norm_num) (by norm_num) (by norm_num)
  rwa [Real.logb_self_eq_one (by norm_num)] at this

/-- The exact odd step on logarithms. -/
theorem logb_tstep_odd_eq {y : ℕ} (hodd : y % 2 = 1) :
    Real.logb 2 (tstep y) =
      Real.logb 2 y - 1 + Real.logb 2 3 + Real.logb 2 (1 + 1 / (3 * (y : ℝ))) := by
  have h2 : 2 * tstep y = 3 * y + 1 := by
    have : tstep y = (3 * y + 1) / 2 := by simp [tstep, hodd]
    omega
  have h2R : (2 : ℝ) * (tstep y : ℝ) = 3 * (y : ℝ) + 1 := by exact_mod_cast h2
  have hyN : 1 ≤ y := by omega
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hyN
  have hy0 : (y : ℝ) ≠ 0 := by linarith
  have hT0 : (tstep y : ℝ) ≠ 0 := by intro h; rw [h] at h2R; linarith
  have hc : (1 + 1 / (3 * (y : ℝ))) ≠ 0 := by positivity
  have key : (2 : ℝ) * (tstep y : ℝ) = (y : ℝ) * 3 * (1 + 1 / (3 * (y : ℝ))) := by
    rw [h2R]; field_simp
  have h := congrArg (Real.logb 2) key
  rw [Real.logb_mul (by norm_num) hT0, Real.logb_mul (mul_ne_zero hy0 (by norm_num)) hc,
    Real.logb_mul hy0 (by norm_num), Real.logb_self_eq_one (by norm_num)] at h
  linarith

/-- `heightCorr` at the next time adds the term of the current height, when it is odd. -/
theorem heightCorr_succ (n t : ℕ) :
    heightCorr n (t + 1) = heightCorr n t + if tstep^[t] n % 2 = 1 then
      Real.logb 2 (1 + 1 / (3 * (tstep^[t] n : ℝ))) else 0 := by
  simp only [heightCorr, Finset.sum_filter, Finset.sum_range_succ]

/-- **The height identity.** -/
theorem height_identity {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    Real.logb 2 (tstep^[t] n) =
      Real.logb 2 n - t + oddCount n t * Real.logb 2 3 + heightCorr n t := by
  induction t with
  | zero => simp [heightCorr, oddCount_zero]
  | succ t ih =>
    have hy := one_le_tstep_iterate hn t
    rw [Function.iterate_succ_apply', oddCount_succ', heightCorr_succ]
    by_cases hodd : tstep^[t] n % 2 = 1
    · rw [logb_tstep_odd_eq hodd, ih, if_pos hodd, if_pos hodd]
      push_cast
      ring
    · have heven : tstep^[t] n % 2 = 0 := by omega
      rw [logb_tstep_even_eq heven hy, ih, if_neg hodd, if_neg hodd]
      push_cast
      ring

/-- One term of `heightCorr` is nonnegative. -/
theorem logb_corr_nonneg {y : ℕ} (hy : 1 ≤ y) : 0 ≤ Real.logb 2 (1 + 1 / (3 * (y : ℝ))) := by
  refine Real.logb_nonneg (by norm_num) ?_
  have : (0 : ℝ) ≤ 1 / (3 * (y : ℝ)) := by positivity
  linarith

/-- `heightCorr` is nonnegative on positive orbits. -/
theorem heightCorr_nonneg {n : ℕ} (hn : 1 ≤ n) (t : ℕ) : 0 ≤ heightCorr n t :=
  Finset.sum_nonneg fun i _ => logb_corr_nonneg (one_le_tstep_iterate hn i)

/-- `heightCorr` grows with the time. -/
theorem heightCorr_mono {n : ℕ} (hn : 1 ≤ n) {s t : ℕ} (hst : s ≤ t) : heightCorr n s ≤ heightCorr n t := by
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.range_mono hst)) fun i _ _ => ?_
  exact logb_corr_nonneg (one_le_tstep_iterate hn i)

/-- The one-letter window at `t` is letter `t`. -/
theorem windowMatch_true_iff (t n : ℕ) :
    WindowMatch (fun s => [true].getD s false) [true].length t n ↔ accWord n t = true := by
  constructor
  · intro hw
    simpa using hw 0 (by simp)
  · intro h s hs
    have hs0 : s = 0 := by simpa using hs
    subst hs0
    simpa using h

/-- Odd letters over a segment, as the single-letter errors by offset. -/
theorem sum_oddCount_eq (C k m : ℕ) :
    (∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), (oddCount n (C * k) : ℝ)) =
      (m : ℝ) * ((C : ℝ) * k) / 2 +
        (∑ t ∈ ((Finset.range (C * k)).filter (fun t => t + [true].length ≤ C * k)).filter
            (fun t => t < k),
          stageError (fun s => [true].getD s false) [true].length k t m) +
        letterExcess C k m := by
  have hN : (∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), oddCount n (C * k)) =
      ∑ t ∈ Finset.range (C * k), ((Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m)).filter
        (WindowMatch (fun s => [true].getD s false) [true].length t)).card := by
    simp_rw [oddCount_eq_sum, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun n _ => ?_
    exact if_congr (windowMatch_true_iff t n).symm rfl rfl
  have hR : (∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), (oddCount n (C * k) : ℝ)) =
      ∑ t ∈ Finset.range (C * k),
        (stageError (fun s => [true].getD s false) [true].length k t m + (m : ℝ) / 2) := by
    have := congrArg (Nat.cast (R := ℝ)) hN
    push_cast at this
    rw [this]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [stageError, List.length_singleton, pow_one]
    ring
  have hF : (Finset.range (C * k)).filter (fun t => t + [true].length ≤ C * k) =
      Finset.range (C * k) := by
    refine Finset.filter_true_of_mem fun t ht => ?_
    have := Finset.mem_range.mp ht
    simpa using this
  have hsplit := stage_sum_split C (fun s => [true].getD s false) [true].length k m
  rw [hR, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hX : letterExcess C k m =
      ∑ t ∈ (Finset.range (C * k)).filter (fun t => k ≤ t ∧ t + [true].length ≤ C * k),
        stageError (fun s => [true].getD s false) [true].length k t m := rfl
  rw [hX]
  rw [hF] at hsplit
  rw [hsplit]
  rw [hF]
  push_cast
  ring

/-- Over a segment of stage `k`, `∑ log₂ n` is within `m` of `m k`. -/
theorem abs_sum_logb_sub_le (k m : ℕ) (hk : 1 ≤ k) (hm : m ≤ 2 ^ (k - 1)) :
    |∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), Real.logb 2 (n : ℝ) - (m : ℝ) * k| ≤ m := by
  have hdbl : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hb : ∀ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m),
      |Real.logb 2 (n : ℝ) - k| ≤ 1 := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hn
    have hn0 : (0 : ℝ) < 2 ^ (k - 1) := by positivity
    have h1R : (2 : ℝ) ^ (k - 1) ≤ n := by exact_mod_cast h1
    have h2R : (n : ℝ) ≤ 2 ^ k := by
      have : n ≤ 2 ^ k := by omega
      exact_mod_cast this
    have hlo := Real.logb_le_logb_of_le (b := 2) (by norm_num) hn0 h1R
    have hhi := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) h2R
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlo hhi
    have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk]; simp
    rw [hc] at hlo
    rw [abs_le]
    constructor <;> linarith
  have hS : ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), Real.logb 2 (n : ℝ) - (m : ℝ) * k =
      ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), (Real.logb 2 (n : ℝ) - k) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    simp
  rw [hS]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hb).trans ?_)
  simp

/-- **The segment identity.**  The sum of heights against the prediction, up to `5 · 2^(k-1)`.  The
offsets below `k` cost `2^k` by Terras, and `log₂ n` is within `1` of `k`. -/
theorem abs_sum_height_sub_le (C : ℕ) (hC : 1 ≤ C) (k m : ℕ) (hk : 1 ≤ k) (hm : m ≤ 2 ^ (k - 1)) :
    |∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), Real.logb 2 (tstep^[C * k] n) -
        m * (heightRate C * k) -
        (Real.logb 2 3 * letterExcess C k m +
          ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), heightCorr n (C * k))| ≤ 5 * 2 ^ (k - 1) := by
  have hsum : ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), Real.logb 2 (tstep^[C * k] n) =
      ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), Real.logb 2 (n : ℝ) -
        (m : ℝ) * ((C : ℝ) * k) +
        (∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), (oddCount n (C * k) : ℝ)) *
          Real.logb 2 3 +
        ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), heightCorr n (C * k) := by
    have hpos : 0 < 2 ^ (k - 1) := by positivity
    rw [Finset.sum_congr rfl fun n hn => height_identity (n := n)
      (le_trans hpos (Finset.mem_Ico.mp hn).1) (C * k)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico,
      nsmul_eq_mul, ← Finset.sum_mul]
    simp only [Nat.add_sub_cancel_left]
    push_cast
    ring
  have hlow := abs_stage_sum_low_le C (fun s => [true].getD s false) [true].length k m
  have hlog := abs_sum_logb_sub_le k m hk hm
  rw [hsum, sum_oddCount_eq]
  set low := ∑ t ∈ ((Finset.range (C * k)).filter (fun t => t + [true].length ≤ C * k)).filter
      (fun t => t < k), stageError (fun s => [true].getD s false) [true].length k t m with hlowdef
  set S := ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), Real.logb 2 (n : ℝ) with hS
  have hdbl : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hmR : (m : ℝ) ≤ 2 ^ (k - 1) := by exact_mod_cast hm
  have hT : (0 : ℝ) < 2 ^ (k - 1) := by positivity
  rw [hdbl] at hlow
  have l1 := one_le_logb_three
  have l2 := logb_three_lt
  have hll : |Real.logb 2 3 * low| ≤ 8 / 5 * (2 * 2 ^ (k - 1)) := by
    rw [abs_mul, abs_of_pos (by linarith : 0 < Real.logb 2 3)]
    exact mul_le_mul l2.le hlow (abs_nonneg _) (by norm_num)
  have heq : S - (m : ℝ) * ((C : ℝ) * k) +
        ((m : ℝ) * ((C : ℝ) * k) / 2 + low + letterExcess C k m) * Real.logb 2 3 +
        ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), heightCorr n (C * k) -
        m * (heightRate C * k) -
        (Real.logb 2 3 * letterExcess C k m +
          ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), heightCorr n (C * k)) =
      (S - (m : ℝ) * k) + Real.logb 2 3 * low := by
    unfold heightRate
    ring
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  linarith

/-- The correction over a segment is at most the correction over the whole stage. -/
theorem sum_corr_segment_le (C k m : ℕ) (hk : 1 ≤ k) (hm : m ≤ 2 ^ (k - 1)) :
    ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), heightCorr n (C * k) ≤
      ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), heightCorr n (C * k) := by
  have hdbl : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : 0 < 2 ^ (k - 1) := by positivity
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega)) ?_
  intro n hn _
  exact heightCorr_nonneg (le_trans hpos (Finset.mem_Ico.mp hn).1) _

/-- The correction over a segment is nonnegative. -/
theorem sum_corr_segment_nonneg (C k m : ℕ) :
    0 ≤ ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m), heightCorr n (C * k) := by
  have hpos : 0 < 2 ^ (k - 1) := by positivity
  exact Finset.sum_nonneg fun n hn => heightCorr_nonneg (le_trans hpos (Finset.mem_Ico.mp hn).1) _

/-- **While the correction is negligible, single-letter balance is the height law.** -/
theorem singleLetterAveraged_iff_meanHeightLaw (C : ℕ) (hC : 1 ≤ C) (h : LowHeightNegligible C) :
    SingleLetterAveraged C ↔ MeanHeightLaw C := by
  have l1 := one_le_logb_three
  have l2 := logb_three_lt
  have habsorb : ∀ δ : ℝ, 0 < δ → ∀ k : ℕ, ⌈20 / δ⌉₊ ≤ k →
      (5 : ℝ) * 2 ^ (k - 1) ≤ δ / 4 * k * 2 ^ (k - 1) := by
    intro δ hδ k hk
    have h1 : 20 / δ ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    rw [div_le_iff₀ hδ] at h1
    have hT : (0 : ℝ) < 2 ^ (k - 1) := by positivity
    refine mul_le_mul_of_nonneg_right ?_ hT.le
    linarith
  constructor
  · intro hS δ hδ
    obtain ⟨K₁, h₁⟩ := hS (δ / 8) (by positivity)
    obtain ⟨K₂, h₂⟩ := h (δ / 4) (by positivity)
    refine ⟨max (max K₁ K₂) (max 1 ⌈20 / δ⌉₊), fun k hk m hm => ?_⟩
    have hk1 : K₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
    have hk2 : K₂ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
    have hk3 : 1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
    have hk4 : ⌈20 / δ⌉₊ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
    have hid := abs_sum_height_sub_le C hC k m hk3 hm
    have hX := h₁ k hk1 m hm
    have hc := (sum_corr_segment_le C k m hk3 hm).trans (h₂ k hk2)
    have hc0 := sum_corr_segment_nonneg C k m
    have hab := habsorb δ hδ k hk4
    have hlX : |Real.logb 2 3 * letterExcess C k m| ≤ 2 * (δ / 8 * k * 2 ^ (k - 1)) := by
      rw [abs_mul, abs_of_pos (by linarith : 0 < Real.logb 2 3)]
      exact mul_le_mul (by linarith) hX (abs_nonneg _) (by norm_num)
    rw [abs_le] at hid hlX ⊢
    constructor <;> linarith [hid.1, hid.2, hlX.1, hlX.2]
  · intro hL δ hδ
    obtain ⟨K₁, h₁⟩ := hL (δ / 4) (by positivity)
    obtain ⟨K₂, h₂⟩ := h (δ / 4) (by positivity)
    refine ⟨max (max K₁ K₂) (max 1 ⌈20 / δ⌉₊), fun k hk m hm => ?_⟩
    have hk1 : K₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
    have hk2 : K₂ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
    have hk3 : 1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
    have hk4 : ⌈20 / δ⌉₊ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
    have hid := abs_sum_height_sub_le C hC k m hk3 hm
    have hH := h₁ k hk1 m hm
    have hc := (sum_corr_segment_le C k m hk3 hm).trans (h₂ k hk2)
    have hc0 := sum_corr_segment_nonneg C k m
    have hab := habsorb δ hδ k hk4
    have hle : |letterExcess C k m| ≤ |Real.logb 2 3 * letterExcess C k m| := by
      rw [abs_mul, abs_of_pos (by linarith : 0 < Real.logb 2 3)]
      exact le_mul_of_one_le_left (abs_nonneg _) l1
    refine hle.trans ?_
    rw [abs_le] at hid hH ⊢
    constructor <;> linarith [hid.1, hid.2, hH.1, hH.2]

/-- Above the threshold the law predicts a negative height, and heights are nonnegative. -/
theorem not_meanHeightLaw_of_five_le (C : ℕ) (hC : 5 ≤ C) : ¬ MeanHeightLaw C := by
  intro hL
  have l2 := logb_three_lt
  have hCR : (5 : ℝ) ≤ C := by exact_mod_cast hC
  have hr : heightRate C < 0 := by
    unfold heightRate
    nlinarith
  obtain ⟨K, hK⟩ := hL (-heightRate C / 2) (by linarith)
  have hk1 : 1 ≤ max K 1 := le_max_right _ _
  set k := max K 1 with hk
  have hb := hK k (le_max_left _ _) (2 ^ (k - 1)) le_rfl
  have hpos : 0 < 2 ^ (k - 1) := by positivity
  have hS : 0 ≤ ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + 2 ^ (k - 1)),
      Real.logb 2 (tstep^[C * k] n) := by
    refine Finset.sum_nonneg fun n hn => Real.logb_nonneg (by norm_num) ?_
    exact_mod_cast one_le_tstep_iterate (le_trans hpos (Finset.mem_Ico.mp hn).1) _
  have hle := (le_abs_self _).trans hb
  push_cast at hle
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have hT : (0 : ℝ) < 2 ^ (k - 1) := by positivity
  have hp : 0 < (-heightRate C) * k * 2 ^ (k - 1) := by
    have : 0 < -heightRate C := by linarith
    positivity
  nlinarith

/-- The first `L` letters of `y`, as a word. -/
def prefixWord (y L : ℕ) : List Bool := (List.range L).map (accWord y)

/-- `prefixWord y L` has `L` letters. -/
theorem prefixWord_length (y L : ℕ) : (prefixWord y L).length = L := by simp [prefixWord]

/-- A visit to `y` at time `i` starts the first `L` letters of `y`. -/
theorem windowMatch_prefixWord {n i y : ℕ} (h : tstep^[i] n = y) (L : ℕ) :
    WindowMatch (fun s => (prefixWord y L).getD s false) (prefixWord y L).length i n := by
  intro s hs
  rw [prefixWord_length] at hs
  have hg : (prefixWord y L).getD s false = accWord y s := by
    simp [prefixWord, List.getD_eq_getElem?_getD, hs]
  show accWord n (i + s) = (prefixWord y L).getD s false
  rw [hg]
  simp only [accWord]
  rw [add_comm, Function.iterate_add_apply, h]

/-- Visits to `y` among the first `t` steps of `n`. -/
def visits (n t y : ℕ) : ℕ := ((Finset.range t).filter fun i => tstep^[i] n = y).card

/-- A term of `heightCorr` at a height `≥ Y` is at most `1 / Y`. -/
theorem logb_corr_le_inv {y Y : ℕ} (hY : 1 ≤ Y) (hy : Y ≤ y) :
    Real.logb 2 (1 + 1 / (3 * (y : ℝ))) ≤ 1 / (Y : ℝ) := by
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hyR : (Y : ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < y := by linarith
  have hlog2 : (1 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl0 : 0 < Real.log 2 := by linarith
  have h1 : Real.log (1 + 1 / (3 * (y : ℝ))) ≤ 1 / (3 * (y : ℝ)) := by
    have hp : (0 : ℝ) < 1 + 1 / (3 * (y : ℝ)) := by positivity
    linarith [Real.log_le_sub_one_of_pos hp]
  have h2 : 1 / (y : ℝ) ≤ 1 / (Y : ℝ) := one_div_le_one_div_of_le hYR hyR
  have h3 : 1 / (3 * (y : ℝ)) = 1 / 3 * (1 / (y : ℝ)) := by field_simp
  have h4 : 0 ≤ 1 / (y : ℝ) := by positivity
  have h5 : 0 ≤ 1 / (Y : ℝ) := by positivity
  rw [Real.logb, div_le_iff₀ hl0, h3]
  rw [h3] at h1
  nlinarith [mul_le_mul_of_nonneg_left hlog2 h5]

/-- Any term of `heightCorr` is at most `1`. -/
theorem logb_corr_le_one {y : ℕ} (hy : 1 ≤ y) : Real.logb 2 (1 + 1 / (3 * (y : ℝ))) ≤ 1 := by
  have := logb_corr_le_inv (y := y) (Y := 1) le_rfl hy
  simpa using this

/-- `heightCorr n t ≤ t / Y + #{i < t : T^i n ≤ Y}`, by the height of each step. -/
theorem heightCorr_le_visits {n : ℕ} (hn : 1 ≤ n) (t Y : ℕ) (hY : 1 ≤ Y) :
    heightCorr n t ≤ (t : ℝ) / Y + ∑ y ∈ Finset.Icc 1 Y, (visits n t y : ℝ) := by
  have hb : ∀ i ∈ Finset.range t,
      (if tstep^[i] n % 2 = 1 then Real.logb 2 (1 + 1 / (3 * (tstep^[i] n : ℝ))) else 0) ≤
        1 / (Y : ℝ) + ∑ y ∈ Finset.Icc 1 Y, (if tstep^[i] n = y then (1 : ℝ) else 0) := by
    intro i _
    have hy := one_le_tstep_iterate hn i
    have hnn : (0 : ℝ) ≤ ∑ y ∈ Finset.Icc 1 Y, (if tstep^[i] n = y then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun y _ => by split_ifs <;> norm_num
    have hYinv : (0 : ℝ) ≤ 1 / (Y : ℝ) := by positivity
    split_ifs with hodd
    · rcases Nat.lt_or_ge (tstep^[i] n) Y with hlt | hge
      · have h1 := Finset.single_le_sum (f := fun y => if tstep^[i] n = y then (1 : ℝ) else 0)
          (fun y _ => by split_ifs <;> norm_num)
          (Finset.mem_Icc.mpr ⟨hy, hlt.le⟩ : tstep^[i] n ∈ Finset.Icc 1 Y)
        simp only [if_true] at h1
        linarith [logb_corr_le_one hy]
      · linarith [logb_corr_le_inv hY hge]
    · linarith
  have hv : ∀ y, (visits n t y : ℝ) =
      ∑ i ∈ Finset.range t, (if tstep^[i] n = y then (1 : ℝ) else 0) := by
    intro y
    simp only [visits, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  unfold heightCorr
  rw [Finset.sum_filter]
  refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp_rw [hv]
  rw [Finset.sum_comm]
  ring

/-- Inside stage `k`, the word of `idx + 1` has `C k` letters. -/
theorem champLen_of_stage (C : ℕ) (hC : 1 ≤ C) {k idx : ℕ} (hk : 1 ≤ k)
    (h1 : 2 ^ (k - 1) ≤ idx + 1) (h2 : idx + 1 < 2 ^ k) : champLen C idx = C * k := by
  rw [champLen, max_eq_left hC]
  congr 1
  apply le_antisymm
  · exact Nat.size_le.mpr h2
  · have : k - 1 < Nat.size (idx + 1) := Nat.lt_size.mpr h1
    omega

/-- Visits to `y` in the first `T` steps are window occurrences, up to the last `L` positions. -/
theorem visits_le_window (n T y L : ℕ) :
    visits n T y ≤ ((Finset.range T).filter fun i =>
        i + (prefixWord y L).length ≤ T ∧
          WindowMatch (fun s => (prefixWord y L).getD s false) (prefixWord y L).length i n).card +
      L := by
  have hsub : (Finset.range T).filter (fun i => tstep^[i] n = y) ⊆
      ((Finset.range T).filter fun i =>
        i + (prefixWord y L).length ≤ T ∧
          WindowMatch (fun s => (prefixWord y L).getD s false) (prefixWord y L).length i n) ∪
        Finset.Ico (T - L) T := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
    have hi1' := Finset.mem_range.mp hi1
    by_cases hfit : i + L ≤ T
    · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi1, ?_, windowMatch_prefixWord hi2 L⟩)
      rwa [prefixWord_length]
    · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, hi1'⟩)
  calc visits n T y ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := by
      refine Nat.add_le_add_left ?_ _
      rw [Nat.card_Ico]
      omega

/-- Visits to `y` over stage `k` are bounded by the interior count of `prefixWord y L`. -/
theorem sum_visits_stage_le (C : ℕ) (hC : 1 ≤ C) (k y L : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), visits n (C * k) y ≤
      interior C (fun s => (prefixWord y L).getD s false) (prefixWord y L).length (2 ^ k - 1) +
        L * 2 ^ (k - 1) := by
  have hdbl : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : 0 < 2 ^ (k - 1) := by positivity
  set W : ℕ → ℕ := fun n => ((Finset.range (C * k)).filter fun i =>
    i + (prefixWord y L).length ≤ C * k ∧
      WindowMatch (fun s => (prefixWord y L).getD s false) (prefixWord y L).length i n).card with hW
  have h1 : ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), visits n (C * k) y ≤
      ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), (W n + L) :=
    Finset.sum_le_sum fun n _ => visits_le_window n (C * k) y L
  have h2 : ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), (W n + L) =
      ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), W n + L * 2 ^ (k - 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul]
    congr 1
    rw [hdbl, mul_comm]
    congr 1
    omega
  have h3 : ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), W n ≤
      interior C (fun s => (prefixWord y L).getD s false) (prefixWord y L).length (2 ^ k - 1) := by
    have e := Finset.sum_Ico_add' W (2 ^ (k - 1) - 1) (2 ^ k - 1) 1
    rw [Nat.sub_add_cancel hpos, Nat.sub_add_cancel (by omega)] at e
    rw [← e]
    unfold interior
    rw [Finset.range_eq_Ico]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun idx hidx => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico (Nat.zero_le (2 ^ (k - 1) - 1)) le_rfl) fun _ _ _ => Nat.zero_le _)
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hidx
    rw [hW, champLen_of_stage C hC hk (by omega) (by omega)]
  omega

/-- **Normality rules out dwelling at bounded height.**  `heightCorr n t ≤ t / Y + #{i < t : y_i ≤ Y}`, and
for each `y ≤ Y` the visits to `y` are occurrences of `prefixWord y L` up to `L` per word, of frequency
`2^(−L)`.  Take `Y` large, then `L` large. -/
theorem lowHeightNegligible_of_normal (C : ℕ) (hC : 1 ≤ C) (h : Normal (collatzChampernowne C)) :
    LowHeightNegligible C := by
  intro δ hδ
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  set Y : ℕ := ⌈3 * (C : ℝ) / δ⌉₊ + 1 with hYdef
  have hY1 : 1 ≤ Y := by omega
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY1
  have hCY : (C : ℝ) / Y ≤ δ / 3 := by
    have h1 : 3 * (C : ℝ) / δ ≤ Y := by
      have : 3 * (C : ℝ) / δ ≤ ⌈3 * (C : ℝ) / δ⌉₊ := Nat.le_ceil _
      rw [hYdef]; push_cast; linarith
    rw [div_le_iff₀ hδ] at h1
    rw [div_le_iff₀ hYR]
    linarith
  set ε : ℝ := δ / (24 * Y * C) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one hεpos (by norm_num : (1 / 2 : ℝ) < 1)
  have hev : ∀ᶠ P : ℕ in atTop, ∀ y ∈ Finset.Icc 1 Y,
      (occ (collatzChampernowne C) (prefixWord y L) P : ℝ) ≤ 2 * ε * P := by
    rw [Filter.eventually_all_finset]
    intro y _
    have ht := h (prefixWord y L)
    rw [prefixWord_length] at ht
    have hlt : (1 / 2 : ℝ) ^ L < 2 * ε := by linarith
    filter_upwards [ht.eventually (gt_mem_nhds hlt), eventually_gt_atTop 0] with P hP hP0
    have hPR : (0 : ℝ) < P := by exact_mod_cast hP0
    rw [div_lt_iff₀ hPR] at hP
    exact hP.le
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hev
  refine ⟨max (max (P₀ + 1) 1) ⌈3 * (Y : ℝ) * L / δ⌉₊, fun k hk => ?_⟩
  have hk1 : P₀ + 1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk2 : 1 ≤ k := by omega
  have hk3 : 3 * (Y : ℝ) * L ≤ δ * k := by
    have h1 : 3 * (Y : ℝ) * L / δ ≤ k :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hk)
    rw [div_le_iff₀ hδ] at h1
    linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk2
  have hT : (0 : ℝ) < 2 ^ (k - 1) := by positivity
  have hdblN : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hdbl : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by exact_mod_cast hdblN
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  have hP : P₀ ≤ cum (champLen C) (2 ^ k - 1) :=
    le_trans (by omega) (le_cum (champLen C) (one_le_champLen C) _)
  have hPup : (cum (champLen C) (2 ^ k - 1) : ℝ) ≤ C * k * (2 * 2 ^ (k - 1)) := by
    have : (cum (champLen C) (2 ^ k - 1) : ℝ) ≤ ((C * k * 2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast cum_stage_end_le C hC k
    push_cast at this
    rwa [hdbl] at this
  -- one height
  have hone : ∀ y ∈ Finset.Icc 1 Y,
      (∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), (visits n (C * k) y : ℝ)) ≤
        δ / (6 * Y) * k * 2 ^ (k - 1) + L * 2 ^ (k - 1) := by
    intro y hy
    have h1 := sum_visits_stage_le C hC k y L hk2
    have h2 := (occ_cum_le C (prefixWord y L) (2 ^ k - 1)).1
    have h3 := hP₀ _ hP y hy
    have h1R : (∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), (visits n (C * k) y : ℝ)) ≤
        (occ (collatzChampernowne C) (prefixWord y L) (cum (champLen C) (2 ^ k - 1)) : ℝ) +
          L * 2 ^ (k - 1) := by
      have : ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), visits n (C * k) y ≤
          occ (collatzChampernowne C) (prefixWord y L) (cum (champLen C) (2 ^ k - 1)) +
            L * 2 ^ (k - 1) := h1.trans (Nat.add_le_add_right h2 _)
      exact_mod_cast this
    have h4 : 2 * ε * (cum (champLen C) (2 ^ k - 1) : ℝ) ≤ δ / (6 * Y) * k * 2 ^ (k - 1) := by
      calc 2 * ε * (cum (champLen C) (2 ^ k - 1) : ℝ) ≤ 2 * ε * (C * k * (2 * 2 ^ (k - 1))) :=
            mul_le_mul_of_nonneg_left hPup (by positivity)
        _ = δ / (6 * Y) * k * 2 ^ (k - 1) := by rw [hε]; field_simp; ring
    linarith
  -- the pointwise bound, summed
  have hpt : ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), heightCorr n (C * k) ≤
      ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k),
        (((C * k : ℕ) : ℝ) / Y + ∑ y ∈ Finset.Icc 1 Y, (visits n (C * k) y : ℝ)) := by
    have hpos : 0 < 2 ^ (k - 1) := by positivity
    exact Finset.sum_le_sum fun n hn =>
      heightCorr_le_visits (le_trans hpos (Finset.mem_Ico.mp hn).1) _ Y hY1
  have hcard : ((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).card : ℝ) = 2 ^ (k - 1) := by
    rw [Nat.card_Ico]
    have : 2 ^ k - 2 ^ (k - 1) = 2 ^ (k - 1) := by omega
    rw [this]
    push_cast
    rfl
  have hsplit : ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k),
        (((C * k : ℕ) : ℝ) / Y + ∑ y ∈ Finset.Icc 1 Y, (visits n (C * k) y : ℝ)) =
      2 ^ (k - 1) * (((C : ℝ) / Y) * k) +
        ∑ y ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), (visits n (C * k) y : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard, Finset.sum_comm]
    push_cast
    ring
  have hY_sum : ∑ y ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k),
        (visits n (C * k) y : ℝ) ≤
      (Y : ℝ) * (δ / (6 * Y) * k * 2 ^ (k - 1) + L * 2 ^ (k - 1)) := by
    refine (Finset.sum_le_card_nsmul _ _ _ hone).trans (le_of_eq ?_)
    simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have e1 : (Y : ℝ) * (δ / (6 * Y) * k * 2 ^ (k - 1) + L * 2 ^ (k - 1)) =
      δ / 6 * k * 2 ^ (k - 1) + (Y * L) * 2 ^ (k - 1) := by
    rw [mul_add, show (Y : ℝ) * (δ / (6 * Y) * k * 2 ^ (k - 1)) = δ / 6 * k * 2 ^ (k - 1) by field_simp]
    ring
  have h5 : (2 : ℝ) ^ (k - 1) * (((C : ℝ) / Y) * k) ≤ 2 ^ (k - 1) * ((δ / 3) * k) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCY hkR.le) hT.le
  have h6 : ((Y : ℝ) * L) * 2 ^ (k - 1) ≤ (δ / 3 * k) * 2 ^ (k - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hT.le
  have h7 : 0 ≤ δ * k * 2 ^ (k - 1) := by positivity
  rw [hsplit] at hpt
  nlinarith

/-- Normality gives the single-letter case. -/
theorem singleLetterAveraged_of_normal (C : ℕ) (hC : 1 ≤ C) (h : Normal (collatzChampernowne C)) :
    SingleLetterAveraged C :=
  fun δ hδ => averagedMixing_of_normal C hC h [true] δ hδ

/-- **A normal `𝒞_C` obeys the height law.** -/
theorem meanHeightLaw_of_normal (C : ℕ) (hC : 1 ≤ C) (h : Normal (collatzChampernowne C)) :
    MeanHeightLaw C :=
  (singleLetterAveraged_iff_meanHeightLaw C hC (lowHeightNegligible_of_normal C hC h)).mp
    (singleLetterAveraged_of_normal C hC h)

end CollatzMoonshot.Conjugacy
