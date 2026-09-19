import CollatzMoonshot.FrontA.FirstCrossingFewRuns

/-! # A stopping-time failure is a stopping-time outlier

If `n` survives its first crossing (so Terras's coefficient stopping-time conjecture fails at
`n`), then `3 · c · n ≤ K^437`, where `K` is the number of odd steps to the crossing and `c` the
Rhin-lite constant.  Since the stopping time exceeds the crossing length, which exceeds `K`, a
counterexample to CST is an orbit that stays above its start for at least `(3cn)^(1/437)`
steps: a polynomial power of `n`, against the ~42·log n the stochastic models predict.
The Diophantine input (Rhin-lite) converts "the start is small" into "the orbit is astronomically
long".  No open hypothesis is used. -/

namespace CollatzMoonshot.FrontA.FirstCrossing

open CollatzMoonshot CollatzMoonshot.FrontB

theorem survivor_ones_pow_ge {n m : ℕ} (hn : n % 2 = 1) (h : At n m)
    (hsurv : n ≤ tstep^[m] n) :
    3 * rhinLiteSepC * (n : ℝ) ≤ ((ones (traceWord n m) : ℕ) : ℝ) ^ 437 := by
  set K := ones (traceWord n m) with hK
  have hK1 : 1 ≤ K := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.1; omega : m ≠ 0)
    have : traceWord n (k + 1) = true :: traceWord (tstep n) k := by simp [traceWord, hn]
    rw [hK, this, ones]; omega
  have hsub : 3 ^ K < 2 ^ m := h.2.2
  have hwin : 2 ^ m < 2 * 3 ^ K := two_pow_lt_two_mul_three_pow h hK1
  have hsmall := small_start_of_not_descending h hsurv
  -- hsmall : 3 * (2^m - 3^K) * n ≤ K * 3^K   (ℕ)
  have hrhin := rhinLite_log23_measure K m hK1 hsub hwin
  have hc := rhinLiteSepC_pos
  -- the linear form is a log, and log x ≤ x - 1
  have h3pos : (0 : ℝ) < 3 ^ K := by positivity
  have hlog : (m : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3
      = Real.log ((2 : ℝ) ^ m / 3 ^ K) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hle : Real.log ((2 : ℝ) ^ m / 3 ^ K) ≤ (2 : ℝ) ^ m / 3 ^ K - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hD : ((2 ^ m - 3 ^ K : ℕ) : ℝ) = (2 : ℝ) ^ m - 3 ^ K := by
    rw [Nat.cast_sub hsub.le]; push_cast; ring
  have hgap : rhinLiteSepC / (K : ℝ) ^ 436 ≤ ((2 ^ m - 3 ^ K : ℕ) : ℝ) / 3 ^ K := by
    rw [hD, sub_div, div_self h3pos.ne']
    linarith [hrhin, hle, hlog]
  have hsmallR : 3 * ((2 ^ m - 3 ^ K : ℕ) : ℝ) * n ≤ (K : ℝ) * 3 ^ K := by
    exact_mod_cast hsmall
  have hKpos : (0 : ℝ) < (K : ℝ) ^ 436 := by positivity
  -- multiply the gap bound by 3 * n * 3^K
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have step : 3 * rhinLiteSepC * n / (K : ℝ) ^ 436 ≤ (K : ℝ) := by
    have := mul_le_mul_of_nonneg_left hgap (by positivity : (0 : ℝ) ≤ 3 * n * 3 ^ K)
    have hl : 3 * (n : ℝ) * 3 ^ K * (rhinLiteSepC / (K : ℝ) ^ 436)
        = 3 * rhinLiteSepC * n / (K : ℝ) ^ 436 * 3 ^ K := by ring
    have hr : 3 * (n : ℝ) * 3 ^ K * (((2 ^ m - 3 ^ K : ℕ) : ℝ) / 3 ^ K)
        = 3 * ((2 ^ m - 3 ^ K : ℕ) : ℝ) * n := by field_simp
    rw [hl, hr] at this
    have := this.trans hsmallR
    exact le_of_mul_le_mul_right this h3pos
  rw [div_le_iff₀ hKpos] at step
  calc 3 * rhinLiteSepC * (n : ℝ) ≤ (K : ℝ) * (K : ℝ) ^ 436 := step
    _ = (K : ℝ) ^ 437 := by ring

end CollatzMoonshot.FrontA.FirstCrossing
