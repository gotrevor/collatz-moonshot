import CollatzMoonshot.FrontA.FirstCrossingRuns

/-! # First crossing: stopping-time correctness with few odd runs

Extends `descends_of_twoRun` from two odd runs to at most four.  The two-sided squeeze is the
same as in the two-run case, but both sides are now carried in `ℝ` because the lower bound
`2^K ≤ (n+1)^(geomS r)` has an irrational exponent built from `logTwoThree = log 3 / log 2`.

* Upper side: `gap_mul_pow_le` (Simons–de Weger Lemma 4) plus `(n+1)^r − n^r ≤ 15 n^(r−1)`
  for `r ≤ 4` gives `D · n ≤ 15 · 3^K`; the Rhin-lite measure `rhinLite_log23_measure` then
  bounds `n` by `15 · K^436 / rhinLiteSepC`, i.e. `log n ≲ 436 log K + 27205`.
* Lower side: telescoping the run head identities in the real numbers gives
  `2^K ≤ (n+1)^(geomS r)` with `geomS 4 ≤ 9.14`, i.e. `log (n+1) ≥ 0.0758 K`.

For `K ≥ 492276` (forced by `ones_ge_of_survives`) the two are incompatible.

This is `StoppingCorrect` restricted to first crossings with at most four maximal odd runs,
conditional on the Rozier–Terracol verified range `CSTVerified`.  It does not prove CST. -/

namespace CollatzMoonshot.FrontA.FirstCrossing

open CollatzMoonshot CollatzMoonshot.FrontB

/-! ## Target 1–2: the last letter of a crossing word is even -/

/-- A first-crossing word ends in `false`: a final odd letter would make
`2^m ≤ 2·3^(K−1) < 3^K`, contradicting the crossing. -/
theorem last_false_of_at {n m : ℕ} (h : At n m) : (traceWord n m).getLast? = some false := by
  sorry

/-- The crossing overshoot is less than a factor `2`: `2^m < 2·3^K`. -/
theorem two_pow_lt_two_mul_three_pow {n m : ℕ} (h : At n m)
    (hK : 1 ≤ ones (traceWord n m)) : 2 ^ m < 2 * 3 ^ ones (traceWord n m) := by
  sorry

/-! ## Target 3: block decomposition with both lengths positive -/

/-- A word that starts odd and ends even decomposes into blocks with *both* components
positive. -/
theorem exists_blockWord_oddRunCount_pos : ∀ v : List Bool, v.head? = some true →
    v.getLast? = some false →
    ∃ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ 0 < p.2) ∧ v = blockWord L ∧
      L.length = oddRunCount v := by
  sorry

/-! ## Target 4: the geometric exponent -/

/-- `log₂ 3`. -/
noncomputable def logTwoThree : ℝ := Real.log 3 / Real.log 2

theorem one_lt_logTwoThree : 1 < logTwoThree := by sorry

theorem logTwoThree_lt : logTwoThree < 159 / 100 := by sorry

/-- `geomS r = 1 + θ + θ² + … + θ^(r−1)` with `θ = log₂ 3`. -/
noncomputable def geomS : ℕ → ℝ
  | 0 => 0
  | r + 1 => 1 + logTwoThree * geomS r

theorem geomS_nonneg (r : ℕ) : 0 ≤ geomS r := by sorry

theorem geomS_four_le : geomS 4 ≤ 914 / 100 := by sorry

theorem geomS_mono : Monotone geomS := by sorry

/-! ## Target 5: the real lower bound on the odd-step count -/

/-- **The run telescoping in `ℝ`.**  Along a block word with all blocks nonempty,
`2^K ≤ (n+1)^(geomS r)`. -/
theorem two_pow_ones_le_rpow (L : List (ℕ × ℕ)) : ∀ n : ℕ, 1 ≤ n →
    (∀ p ∈ L, 0 < p.1 ∧ 0 < p.2) → traceWord n (blockWord L).length = blockWord L →
    (2 : ℝ) ^ ones (blockWord L) ≤ ((n : ℝ) + 1) ^ geomS L.length := by
  sorry

/-! ## Target 6: the upper side -/

/-- With at most four odd runs, the Simons–de Weger bound reads `D · n ≤ 15 · 3^K`. -/
theorem gap_mul_le_fifteen {n m : ℕ} (hn : n % 2 = 1) (h : At n m) (hsurv : n ≤ tstep^[m] n)
    (hr : oddRunCount (traceWord n m) ≤ 4) :
    (2 ^ m - 3 ^ ones (traceWord n m)) * n ≤ 15 * 3 ^ ones (traceWord n m) := by
  sorry

/-! ## Target 7: stopping-time correctness on few-run crossings -/

theorem descends_of_oddRunCount_le_four (hv : CSTVerified) {n m : ℕ} (hn : 2 ≤ n)
    (h : At n m) (hr : oddRunCount (traceWord n m) ≤ 4) : tstep^[m] n < n := by
  sorry

end CollatzMoonshot.FrontA.FirstCrossing
