import CollatzMoonshot.FrontA.FirstCrossingFewRuns

/-! # Verified digits of `log 2`, `log 3`, `log₂ 3`, and brackets at any scale

The repository certifies a bracket `2^a < 3^b` by a `native_decide` power comparison, which
stops being feasible around `b ~ 10^7` (`pow_cert_10781274` already compares five-million-digit
numerals).  Forty-four verified decimal digits of `log 2` and `log 3`, obtained from the
Taylor remainder bound `Real.abs_log_sub_add_sum_range_le`, certify the same brackets by
*rational arithmetic* at any scale.

With the bracket moved from denominators `~5·10^5` to `~6·10^15` the strong separation
`3^k ≤ (2^m − 3^k)·2^58` holds for all `k < 6234549927241963`, and the pincer of
`descends_of_oddRunCount_le_four` extends from four odd runs to fifty. -/

namespace CollatzMoonshot.FrontA.FirstCrossing

open CollatzMoonshot CollatzMoonshot.FrontB Finset

set_option maxRecDepth 100000

/-! ## Targets 1–3: verified digits -/

/-- Forty-four verified digits of `Real.log 2`. -/
theorem log_two_bounds :
    (69314718055994530941723212145817656807550013 : ℝ) / 10 ^ 44 < Real.log 2 ∧
      Real.log 2 < (69314718055994530941723212145817656807550015 : ℝ) / 10 ^ 44 := by
  have habs : |(1:ℝ)/2| = 1/2 := by rw [abs_of_pos] <;> norm_num
  have h := Real.abs_log_sub_add_sum_range_le (x := (1:ℝ)/2) (by rw [habs]; norm_num) 150
  rw [habs, show (1:ℝ) - 1/2 = 1/2 by norm_num,
    show Real.log ((1:ℝ)/2) = -Real.log 2 by rw [one_div, Real.log_inv], abs_le] at h
  have hrem : ((1:ℝ)/2) ^ (150 + 1) / (1 - 1/2) ≤ 1 / 10 ^ 45 := by norm_num
  have hlo : (69314718055994530941723212145817656807550013 : ℝ) / 10 ^ 44 + 1 / 10 ^ 45
      < ∑ i ∈ range 150, ((1:ℝ)/2) ^ (i + 1) / (i + 1) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hhi : (∑ i ∈ range 150, ((1:ℝ)/2) ^ (i + 1) / (i + 1)) + 1 / 10 ^ 45
      < (69314718055994530941723212145817656807550015 : ℝ) / 10 ^ 44 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩

/-- Forty-four verified digits of `Real.log 3`.  Both Taylor remainders are kept symbolic
until the very end: routing through the *rounded* `log_two_bounds` would lose `1.6·10^-45`
and the frozen upper digit `…057` has only `2.2·10^-45` of slack. -/
theorem log_three_bounds :
    (109861228866810969139524523692252570464749055 : ℝ) / 10 ^ 44 < Real.log 3 ∧
      Real.log 3 < (109861228866810969139524523692252570464749057 : ℝ) / 10 ^ 44 := by
  have habs2 : |(1:ℝ)/2| = 1/2 := by rw [abs_of_pos] <;> norm_num
  have h2 := Real.abs_log_sub_add_sum_range_le (x := (1:ℝ)/2) (by rw [habs2]; norm_num) 150
  rw [habs2, show (1:ℝ) - 1/2 = 1/2 by norm_num,
    show Real.log ((1:ℝ)/2) = -Real.log 2 by rw [one_div, Real.log_inv], abs_le] at h2
  have habs3 : |(1:ℝ)/3| = 1/3 := by rw [abs_of_pos] <;> norm_num
  have h3 := Real.abs_log_sub_add_sum_range_le (x := (1:ℝ)/3) (by rw [habs3]; norm_num) 96
  rw [habs3, show (1:ℝ) - 1/3 = 2/3 by norm_num,
    show Real.log ((2:ℝ)/3) = Real.log 2 - Real.log 3 by
      rw [Real.log_div (by norm_num) (by norm_num)], abs_le] at h3
  have hrem : ((1:ℝ)/2) ^ (150 + 1) / (1/2) + ((1:ℝ)/3) ^ (96 + 1) / (2/3) ≤ 1 / 10 ^ 45 := by
    norm_num
  have hrem2 : (0:ℝ) ≤ ((1:ℝ)/2) ^ (150 + 1) / (1/2) := by positivity
  have hrem3 : (0:ℝ) ≤ ((1:ℝ)/3) ^ (96 + 1) / (2/3) := by positivity
  have hlo : (109861228866810969139524523692252570464749055 : ℝ) / 10 ^ 44 + 1 / 10 ^ 45
      < (∑ i ∈ range 150, ((1:ℝ)/2) ^ (i + 1) / (i + 1))
        + ∑ i ∈ range 96, ((1:ℝ)/3) ^ (i + 1) / (i + 1) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hhi : (∑ i ∈ range 150, ((1:ℝ)/2) ^ (i + 1) / (i + 1))
        + (∑ i ∈ range 96, ((1:ℝ)/3) ^ (i + 1) / (i + 1)) + 1 / 10 ^ 45
      < (109861228866810969139524523692252570464749057 : ℝ) / 10 ^ 44 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  exact ⟨by linarith [h2.1, h2.2, h3.1, h3.2], by linarith [h2.1, h2.2, h3.1, h3.2]⟩

/-- Verified digits of `logTwoThree = log 3 / log 2`. -/
theorem logTwoThree_bounds :
    (109861228866810969139524523692252570464749055 : ℝ) /
        69314718055994530941723212145817656807550015 < logTwoThree ∧
      logTwoThree < (109861228866810969139524523692252570464749057 : ℝ) /
        69314718055994530941723212145817656807550013 := by
  obtain ⟨h2lo, h2hi⟩ := log_two_bounds
  obtain ⟨h3lo, h3hi⟩ := log_three_bounds
  have h2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [logTwoThree]
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) h2pos]; nlinarith
  · rw [div_lt_div_iff₀ h2pos (by norm_num)]; nlinarith

/-! ## Target 4: brackets by rational arithmetic -/

theorem two_pow_lt_three_pow_of_lt {a b : ℕ} (hb : 0 < b)
    (h : (a : ℝ) / b < (109861228866810969139524523692252570464749055 : ℝ) /
      69314718055994530941723212145817656807550015) :
    2 ^ a < 3 ^ b := by
  refine (lt_logb_two_three_iff a b hb).mp ?_
  rw [show Real.logb 2 3 = logTwoThree by rw [Real.logb, logTwoThree]]
  exact h.trans logTwoThree_bounds.1

theorem three_pow_lt_two_pow_of_lt {c d : ℕ} (hd : 0 < d)
    (h : (109861228866810969139524523692252570464749057 : ℝ) /
      69314718055994530941723212145817656807550013 < (c : ℝ) / d) :
    3 ^ d < 2 ^ c := by
  refine (logb_two_three_lt_iff c d hd).mp ?_
  rw [show Real.logb 2 3 = logTwoThree by rw [Real.logb, logTwoThree]]
  exact logTwoThree_bounds.2.trans h

/-! ## Target 5: the strong bracket at the `6·10^15` scale -/

theorem sep_strong_6e15 (k m : ℕ) (hk : 0 < k) (hklt : k < 6234549927241963)
    (h1 : 3 ^ k < 2 ^ m) : 3 ^ k ≤ (2 ^ m - 3 ^ k) * 2 ^ 58 :=
  sep_strong_of_bracket_nat k m 766512153894657 483615324366283
    9115015689657667 5750934602875680
    9881527843552324 6234549927241963
    206745572560704147 130441933147714940 58 hk h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (two_pow_lt_three_pow_of_lt (by norm_num) (by push_cast; norm_num))
    (three_pow_lt_two_pow_of_lt (by norm_num) (by push_cast; norm_num))
    (two_pow_lt_three_pow_of_lt (by norm_num) (by push_cast; norm_num))
    (three_pow_lt_two_pow_of_lt (by norm_num) (by push_cast; norm_num))
    (by norm_num) (by norm_num) (by omega) (by norm_num) (by norm_num)

/-! ## Targets 6–7: the upper side with a general run count -/

theorem succ_pow_sub_le_runs (n r : ℕ) (hn : 2 * r * r ≤ n) (hr : 1 ≤ r) :
    (n + 1) ^ r - n ^ r ≤ (r + 1) * n ^ (r - 1) := by
  sorry

theorem gap_mul_le_runs_succ {n m : ℕ} (hn : n % 2 = 1) (h : At n m) (hsurv : n ≤ tstep^[m] n)
    (hbig : 2 * oddRunCount (traceWord n m) * oddRunCount (traceWord n m) ≤ n) :
    (2 ^ m - 3 ^ ones (traceWord n m)) * n ≤
      (oddRunCount (traceWord n m) + 1) * 3 ^ ones (traceWord n m) := by
  sorry

/-! ## Target 8: the raised threshold -/

theorem ones_ge_of_survives_6e15 (hv : CSTVerified) {n m : ℕ} (hn : 2 ≤ n) (h : At n m)
    (hsurv : n ≤ tstep^[m] n) (hr : oddRunCount (traceWord n m) ≤ 96) :
    6234549927241963 ≤ ones (traceWord n m) := by
  sorry

/-! ## Target 9: stopping-time correctness with at most fifty odd runs -/

theorem descends_of_oddRunCount_le_fifty (hv : CSTVerified) {n m : ℕ} (hn : 2 ≤ n)
    (h : At n m) (hr : oddRunCount (traceWord n m) ≤ 50) : tstep^[m] n < n := by
  sorry

end CollatzMoonshot.FrontA.FirstCrossing
