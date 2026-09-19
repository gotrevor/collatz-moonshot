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
  sorry

/-- Forty-four verified digits of `Real.log 3`. -/
theorem log_three_bounds :
    (109861228866810969139524523692252570464749055 : ℝ) / 10 ^ 44 < Real.log 3 ∧
      Real.log 3 < (109861228866810969139524523692252570464749057 : ℝ) / 10 ^ 44 := by
  sorry

/-- Verified digits of `logTwoThree = log 3 / log 2`. -/
theorem logTwoThree_bounds :
    (109861228866810969139524523692252570464749055 : ℝ) /
        69314718055994530941723212145817656807550015 < logTwoThree ∧
      logTwoThree < (109861228866810969139524523692252570464749057 : ℝ) /
        69314718055994530941723212145817656807550013 := by
  sorry

/-! ## Target 4: brackets by rational arithmetic -/

theorem two_pow_lt_three_pow_of_lt {a b : ℕ} (hb : 0 < b)
    (h : (a : ℝ) / b < (109861228866810969139524523692252570464749055 : ℝ) /
      69314718055994530941723212145817656807550015) :
    2 ^ a < 3 ^ b := by
  sorry

theorem three_pow_lt_two_pow_of_lt {c d : ℕ} (hd : 0 < d)
    (h : (109861228866810969139524523692252570464749057 : ℝ) /
      69314718055994530941723212145817656807550013 < (c : ℝ) / d) :
    3 ^ d < 2 ^ c := by
  sorry

/-! ## Target 5: the strong bracket at the `6·10^15` scale -/

theorem sep_strong_6e15 (k m : ℕ) (hk : 0 < k) (hklt : k < 6234549927241963)
    (h1 : 3 ^ k < 2 ^ m) : 3 ^ k ≤ (2 ^ m - 3 ^ k) * 2 ^ 58 := by
  sorry

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
