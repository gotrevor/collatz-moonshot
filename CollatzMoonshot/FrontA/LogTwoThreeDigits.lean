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

/-- **Scaled Bernoulli.**  `n²(n+1)^r ≤ (n² + rn + r²)n^r` whenever `2r² ≤ n`.  The
square-scaled form is what makes the induction close: with the naive `n(n+1)^r ≤ (n+r+1)n^r`
the step loses exactly the `+1`, while here the step reduces to `r² ≤ (r+1)n`. -/
theorem sq_mul_succ_pow_le (n : ℕ) : ∀ r : ℕ, 2 * r * r ≤ n →
    n ^ 2 * (n + 1) ^ r ≤ (n ^ 2 + r * n + r * r) * n ^ r := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
      intro hbig
      have hr2 : 2 * r * r ≤ n := by nlinarith
      have hstep := ih hr2
      have hmul : n ^ 2 * (n + 1) ^ (r + 1)
          ≤ ((n ^ 2 + r * n + r * r) * n ^ r) * (n + 1) := by
        calc n ^ 2 * (n + 1) ^ (r + 1) = (n ^ 2 * (n + 1) ^ r) * (n + 1) := by ring
          _ ≤ ((n ^ 2 + r * n + r * r) * n ^ r) * (n + 1) :=
              Nat.mul_le_mul_right _ hstep
      refine hmul.trans ?_
      have hkey : r * r ≤ (r + 1) * n := by nlinarith
      have : (n ^ 2 + r * n + r * r) * (n + 1)
          ≤ (n ^ 2 + (r + 1) * n + (r + 1) * (r + 1)) * n := by nlinarith
      calc ((n ^ 2 + r * n + r * r) * n ^ r) * (n + 1)
          = ((n ^ 2 + r * n + r * r) * (n + 1)) * n ^ r := by ring
        _ ≤ ((n ^ 2 + (r + 1) * n + (r + 1) * (r + 1)) * n) * n ^ r :=
            Nat.mul_le_mul_right _ this
        _ = (n ^ 2 + (r + 1) * n + (r + 1) * (r + 1)) * n ^ (r + 1) := by ring

/-- `(n+1)^r − n^r ≤ (r+1)n^(r−1)` once `2r² ≤ n`.  This is the run-count generalisation of
`succ_pow_sub_le` (which is the `r ≤ 4`, constant-15 version). -/
theorem succ_pow_sub_le_runs (n r : ℕ) (hn : 2 * r * r ≤ n) (hr : 1 ≤ r) :
    (n + 1) ^ r - n ^ r ≤ (r + 1) * n ^ (r - 1) := by
  have hnpos : 0 < n := by nlinarith
  have hA := sq_mul_succ_pow_le n r hn
  have hsplit : n ^ r = n * n ^ (r - 1) := by
    conv_lhs => rw [show r = 1 + (r - 1) by omega]
    rw [pow_add, pow_one]
  have hcoef : r * n + r * r ≤ (r + 1) * n := by nlinarith
  have hmain : n ^ 2 * (n + 1) ^ r ≤ n ^ 2 * (n ^ r + (r + 1) * n ^ (r - 1)) := by
    refine hA.trans ?_
    calc (n ^ 2 + r * n + r * r) * n ^ r
        = n ^ 2 * n ^ r + (r * n + r * r) * n ^ r := by ring
      _ ≤ n ^ 2 * n ^ r + ((r + 1) * n) * n ^ r := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hcoef) _
      _ = n ^ 2 * n ^ r + (r + 1) * (n * n ^ (r - 1)) * n := by rw [← hsplit]; ring
      _ = n ^ 2 * (n ^ r + (r + 1) * n ^ (r - 1)) := by rw [hsplit]; ring
  have := Nat.le_of_mul_le_mul_left hmain (by positivity)
  omega

theorem gap_mul_le_runs_succ {n m : ℕ} (hn : n % 2 = 1) (h : At n m) (hsurv : n ≤ tstep^[m] n)
    (hbig : 2 * oddRunCount (traceWord n m) * oddRunCount (traceWord n m) ≤ n) :
    (2 ^ m - 3 ^ ones (traceWord n m)) * n ≤
      (oddRunCount (traceWord n m) + 1) * 3 ^ ones (traceWord n m) := by
  have hb := gap_mul_pow_le hn h hsurv
  set K := ones (traceWord n m) with hKdef
  set r := oddRunCount (traceWord n m) with hrdef
  set D := 2 ^ m - 3 ^ K with hD
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · have hD0 : D = 0 := by rw [hr0] at hb; simpa using hb
    rw [hD0]; simp
  · have hn1 : 1 ≤ n := by nlinarith
    have hexp : (n + 1) ^ r - n ^ r ≤ (r + 1) * n ^ (r - 1) :=
      succ_pow_sub_le_runs n r hbig hr1
    have hsplit : n ^ r = n * n ^ (r - 1) := by
      conv_lhs => rw [show r = 1 + (r - 1) by omega]
      rw [pow_add, pow_one]
    have hchain : (D * n) * n ^ (r - 1) ≤ ((r + 1) * 3 ^ K) * n ^ (r - 1) := by
      calc (D * n) * n ^ (r - 1) = D * n ^ r := by rw [hsplit]; ring
        _ ≤ 3 ^ K * ((n + 1) ^ r - n ^ r) := hb
        _ ≤ 3 ^ K * ((r + 1) * n ^ (r - 1)) := Nat.mul_le_mul_left _ hexp
        _ = ((r + 1) * 3 ^ K) * n ^ (r - 1) := by ring
    exact Nat.le_of_mul_le_mul_right hchain (by positivity)

/-! ## Target 8: the raised threshold -/

theorem ones_ge_of_survives_6e15 (hv : CSTVerified) {n m : ℕ} (hn : 2 ≤ n) (h : At n m)
    (hsurv : n ≤ tstep^[m] n) (hr : oddRunCount (traceWord n m) ≤ 96) :
    6234549927241963 ≤ ones (traceWord n m) := by
  by_contra hlt
  push_neg at hlt
  set K := ones (traceWord n m) with hK
  have hodd : n % 2 = 1 := by
    rcases Nat.even_or_odd n with he | ho
    · exact absurd (descends_of_even hn (Nat.even_iff.mp he) h) (by omega)
    · exact Nat.odd_iff.mp ho
  have hsub : 3 ^ K < 2 ^ m := h.2.2
  have hnbig : 18432 ≤ n := by
    by_contra hsmall
    push_neg at hsmall
    exact absurd (hv n m hn (by omega) h) (by omega)
  have hbig : 2 * oddRunCount (traceWord n m) * oddRunCount (traceWord n m) ≤ n := by
    nlinarith [hr, hnbig]
  rcases Nat.eq_zero_or_pos K with h0 | hpos
  · have hid := tstep_iterate_identity m n
    rw [← hK, h0, pow_zero, one_mul,
      numer_eq_zero_of_ones_eq_zero (by rw [← hK, h0])] at hid
    have h2m : 2 ≤ 2 ^ m := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h.1
    have : 2 * n ≤ 2 ^ m * tstep^[m] n := by
      calc 2 * n ≤ 2 * tstep^[m] n := by omega
        _ ≤ 2 ^ m * tstep^[m] n := Nat.mul_le_mul_right _ h2m
    omega
  · have hsep := sep_strong_6e15 K m hpos hlt hsub
    have hgap := gap_mul_le_runs_succ hodd h hsurv hbig
    rw [← hK] at hgap
    set D := 2 ^ m - 3 ^ K with hD
    have hDpos : 0 < D := by omega
    have hr97 : oddRunCount (traceWord n m) + 1 ≤ 97 := by omega
    have hchain : D * n ≤ 97 * (D * 2 ^ 58) :=
      hgap.trans ((Nat.mul_le_mul_right _ hr97).trans (Nat.mul_le_mul_left _ hsep))
    have hnle : n ≤ 97 * 2 ^ 58 := by
      have : D * n ≤ D * (97 * 2 ^ 58) := by
        calc D * n ≤ 97 * (D * 2 ^ 58) := hchain
          _ = D * (97 * 2 ^ 58) := by ring
      exact Nat.le_of_mul_le_mul_left this hDpos
    exact absurd (hv n m hn (by norm_num at hnle ⊢; omega) h) (by omega)

/-! ## Target 9: stopping-time correctness with at most fifty odd runs -/

/-- Closed form for the geometric sum `geomS r = 1 + θ + … + θ^(r−1)`, `θ = logTwoThree`. -/
theorem geomS_mul_sub_one : ∀ r : ℕ, geomS r * (logTwoThree - 1) = logTwoThree ^ r - 1 := by
  intro r
  induction r with
  | zero => simp [geomS]
  | succ r ih =>
      have hdef : geomS (r + 1) = 1 + logTwoThree * geomS r := rfl
      rw [hdef]
      linear_combination logTwoThree * ih

theorem geomS_fifty_le : geomS 50 ≤ 21 * 10 ^ 9 := by
  have hlo : (158 / 100 : ℝ) < logTwoThree := lt_trans (by norm_num) logTwoThree_bounds.1
  have hhi : logTwoThree ≤ 159 / 100 := logTwoThree_lt.le
  have hpow : logTwoThree ^ 50 ≤ (159 / 100 : ℝ) ^ 50 :=
    pow_le_pow_left₀ (by linarith) hhi 50
  have hnum : (159 / 100 : ℝ) ^ 50 ≤ 11745086403 := by norm_num
  have heq := geomS_mul_sub_one 50
  have hnn := geomS_nonneg 50
  nlinarith [heq, hnn, hpow, hnum, hlo]

theorem log_fiftyone_le : Real.log 51 ≤ 416 / 100 := by
  have h1 : Real.log 51 ≤ Real.log 64 := Real.log_le_log (by norm_num) (by norm_num)
  have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_lt_d9
  rw [h64] at h1
  linarith

/-- `log 6234549927241963 ≤ 36.4`, via `log t ≤ t − 1` at `t = K₀/(3·2^51) ≈ 0.923`. -/
theorem log_K0_le : Real.log 6234549927241963 ≤ 364 / 10 := by
  have h1 : Real.log ((6234549927241963 : ℝ) / 6755399441055744)
      ≤ (6234549927241963 : ℝ) / 6755399441055744 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num)] at h1
  have hsplit : Real.log (6755399441055744 : ℝ) = Real.log 3 + 51 * Real.log 2 := by
    rw [show (6755399441055744 : ℝ) = 3 * 2 ^ (51 : ℕ) by norm_num,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  have h2 := Real.log_two_lt_d9
  have h3 := log_three_bounds.2
  rw [hsplit] at h1
  norm_num at h1 ⊢
  linarith

/-- **Stopping-time correctness on first crossings with at most fifty odd runs.**  Same
two-sided squeeze as `descends_of_oddRunCount_le_four`, run at the `6·10^15` bracket:
`geomS 50 ≤ 2.03·10^10` costs a factor `2.2·10^9` on the lower side, and the raised
threshold `K ≥ 6.23·10^15` from `ones_ge_of_survives_6e15` pays for it with a factor ~5
of margin to spare. -/
theorem descends_of_oddRunCount_le_fifty (hv : CSTVerified) {n m : ℕ} (hn : 2 ≤ n)
    (h : At n m) (hr : oddRunCount (traceWord n m) ≤ 50) : tstep^[m] n < n := by
  rcases Nat.even_or_odd n with heven | hoddN
  · exact descends_of_even hn (Nat.even_iff.mp heven) h
  have hodd : n % 2 = 1 := Nat.odd_iff.mp hoddN
  by_contra hcon
  push_neg at hcon
  set K := ones (traceWord n m) with hKdef
  have hK : 6234549927241963 ≤ K := ones_ge_of_survives_6e15 hv hn h hcon (by omega)
  have hw1 : 3 ^ K < 2 ^ m := h.2.2
  have hw2 : 2 ^ m < 2 * 3 ^ K := two_pow_lt_two_mul_three_pow h (by omega)
  have hnbig : 5000 ≤ n := by
    by_contra hsmall
    push_neg at hsmall
    exact absurd (hv n m hn (by omega) h) (by omega)
  have hbig : 2 * oddRunCount (traceWord n m) * oddRunCount (traceWord n m) ≤ n := by
    nlinarith [hr, hnbig]
  have hgapnat := gap_mul_le_runs_succ hodd h hcon hbig
  rw [← hKdef] at hgapnat
  have hgapnat' : (2 ^ m - 3 ^ K) * n ≤ 51 * 3 ^ K :=
    hgapnat.trans (Nat.mul_le_mul_right _ (by omega))
  set Kr : ℝ := (K : ℝ) with hKr
  set nr : ℝ := (n : ℝ) with hnr
  have hnr2 : (2 : ℝ) ≤ nr := by rw [hnr]; exact_mod_cast hn
  have hnrpos : (0 : ℝ) < nr := by linarith
  have hKrge : (6234549927241963 : ℝ) ≤ Kr := by rw [hKr]; exact_mod_cast hK
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ K := by positivity
  -- ### upper side
  have hmeas := rhinLite_log23_measure K m (by omega) hw1 hw2
  have hratio : (m : ℝ) * Real.log 2 - Kr * Real.log 3
      = Real.log ((2 : ℝ) ^ m / (3 : ℝ) ^ K) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hle1 : Real.log ((2 : ℝ) ^ m / (3 : ℝ) ^ K) ≤ (2 : ℝ) ^ m / (3 : ℝ) ^ K - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hcast : (((2 ^ m - 3 ^ K : ℕ)) : ℝ) = (2 : ℝ) ^ m - (3 : ℝ) ^ K := by
    rw [Nat.cast_sub hw1.le]; push_cast; ring
  have hgapR : ((2 : ℝ) ^ m - (3 : ℝ) ^ K) * nr ≤ 51 * (3 : ℝ) ^ K := by
    have hc : (((2 ^ m - 3 ^ K : ℕ) * n : ℕ) : ℝ) ≤ ((51 * 3 ^ K : ℕ) : ℝ) := by
      exact_mod_cast hgapnat'
    push_cast [hcast] at hc
    rw [hnr]; linarith
  have hfrac : (2 : ℝ) ^ m / (3 : ℝ) ^ K - 1 ≤ 51 / nr := by
    rw [show (2 : ℝ) ^ m / (3 : ℝ) ^ K - 1 = ((2 : ℝ) ^ m - (3 : ℝ) ^ K) / (3 : ℝ) ^ K by
      field_simp, div_le_div_iff₀ h3pos hnrpos]
    linarith
  have hmeas2 : rhinLiteSepC / Kr ^ 436 ≤ 51 / nr := by
    calc rhinLiteSepC / Kr ^ 436 ≤ (m : ℝ) * Real.log 2 - Kr * Real.log 3 := hmeas
      _ = Real.log ((2 : ℝ) ^ m / (3 : ℝ) ^ K) := hratio
      _ ≤ (2 : ℝ) ^ m / (3 : ℝ) ^ K - 1 := hle1
      _ ≤ 51 / nr := hfrac
  have hKrpos : (0 : ℝ) < Kr := by linarith
  have hprod : nr * rhinLiteSepC ≤ 51 * Kr ^ 436 := by
    rw [div_le_div_iff₀ (by positivity) hnrpos] at hmeas2
    linarith
  have hUlog : Real.log nr + Real.log rhinLiteSepC ≤ Real.log 51 + 436 * Real.log Kr := by
    have h1 : Real.log (nr * rhinLiteSepC) ≤ Real.log (51 * Kr ^ 436) :=
      Real.log_le_log (mul_pos hnrpos rhinLiteSepC_pos) hprod
    rw [Real.log_mul hnrpos.ne' rhinLiteSepC_pos.ne',
      Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    push_cast at h1
    linarith
  have hU : Real.log nr ≤ 416 / 100 + 436 * Real.log Kr + 27203 := by
    have := log_fiftyone_le
    have := log_rhinLiteSepC_ge
    linarith
  have hlogK : Real.log Kr ≤ 364 / 10 + Kr / 6234549927241963 - 1 := by
    have h1 : Real.log (Kr / 6234549927241963) ≤ Kr / 6234549927241963 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hKrpos.ne' (by norm_num)] at h1
    have := log_K0_le
    linarith
  -- ### lower side
  have hhead : (traceWord n m).head? = some true := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.1; omega : m ≠ 0)
    rw [hk]; simp [traceWord, hodd]
  obtain ⟨L, hposL, hword, hcount⟩ :=
    exists_blockWord_oddRunCount_pos _ hhead (last_false_of_at h)
  have hlenm : m = (blockWord L).length := by
    have := congrArg List.length hword; simpa using this
  have htrace : traceWord n (blockWord L).length = blockWord L := by rw [← hlenm, hword]
  have hbound := two_pow_ones_le_rpow L n (by omega) hposL htrace
  have honesL : ones (blockWord L) = K := by rw [hKdef, hword]
  have hLlen : L.length ≤ 50 := by rw [hcount]; exact hr
  have hNge : (1 : ℝ) ≤ nr + 1 := by linarith
  have hexp : ((nr : ℝ) + 1) ^ geomS L.length ≤ ((nr : ℝ) + 1) ^ geomS 50 :=
    Real.rpow_le_rpow_of_exponent_le hNge (geomS_mono hLlen)
  have hlow0 : (2 : ℝ) ^ K ≤ ((nr : ℝ) + 1) ^ geomS 50 := by
    rw [← honesL]; exact le_trans hbound hexp
  have hlogn1 : 0 ≤ Real.log (nr + 1) := Real.log_nonneg (by linarith)
  have hL1 : Kr * Real.log 2 ≤ geomS 50 * Real.log (nr + 1) := by
    have h1 : Real.log ((2 : ℝ) ^ K) ≤ Real.log (((nr : ℝ) + 1) ^ geomS 50) :=
      Real.log_le_log (by positivity) hlow0
    rw [Real.log_pow, Real.log_rpow (by linarith)] at h1
    rw [hKr]; exact_mod_cast h1
  have hL2 : Kr * Real.log 2 ≤ (21 * 10 ^ 9 : ℝ) * Real.log (nr + 1) := by
    have := geomS_fifty_le
    nlinarith
  have hL3 : Kr * (6931471803 / 10 ^ 10) ≤ (21 * 10 ^ 9 : ℝ) * Real.log (nr + 1) := by
    have h2 := Real.log_two_gt_d9
    nlinarith
  have hsplit : Real.log (nr + 1) ≤ Real.log 2 + Real.log nr := by
    have h1 : Real.log (nr + 1) ≤ Real.log (2 * nr) := Real.log_le_log (by linarith) (by linarith)
    rwa [Real.log_mul (by norm_num) hnrpos.ne'] at h1
  have h2hi := Real.log_two_lt_d9
  linarith

end CollatzMoonshot.FrontA.FirstCrossing
