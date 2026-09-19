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
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.1; omega : m ≠ 0)
  have hsplit : traceWord n (j + 1) = traceWord n j ++ [decide (tstep^[j] n % 2 = 1)] := by
    rw [traceWord_add]; rfl
  rw [hsplit, List.getLast?_concat]
  simp only [Option.some.injEq, decide_eq_false_iff_not]
  intro hodd
  have hones : ones (traceWord n (j + 1)) = ones (traceWord n j) + 1 := by
    rw [hsplit, ones_append]; simp [hodd, ones]
  have hpre := h.2.1 j (by omega)
  have hsub := h.2.2
  rw [hones] at hsub
  have : (3 : ℕ) ^ (ones (traceWord n j) + 1) = 3 * 3 ^ ones (traceWord n j) := by ring
  rw [this, pow_succ] at hsub
  omega

/-- The crossing overshoot is less than a factor `2`: `2^m < 2·3^K`. -/
theorem two_pow_lt_two_mul_three_pow {n m : ℕ} (h : At n m)
    (hK : 1 ≤ ones (traceWord n m)) : 2 ^ m < 2 * 3 ^ ones (traceWord n m) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.1; omega : m ≠ 0)
  have hlast := last_false_of_at h
  have hsplit : traceWord n (j + 1) = traceWord n j ++ [decide (tstep^[j] n % 2 = 1)] := by
    rw [traceWord_add]; rfl
  have hb : decide (tstep^[j] n % 2 = 1) = false := by
    rw [hsplit, List.getLast?_concat] at hlast
    simpa using hlast
  have hones : ones (traceWord n (j + 1)) = ones (traceWord n j) := by
    rw [hsplit, ones_append, hb]; simp [ones]
  have hpre := h.2.1 j (by omega)
  rw [hones] at hK ⊢
  rcases Nat.lt_or_ge (2 ^ j) (3 ^ ones (traceWord n j)) with hlt | hge
  · rw [pow_succ]; omega
  · have heq : (2 : ℕ) ^ j = 3 ^ ones (traceWord n j) := le_antisymm hpre hge
    exfalso
    have h3 : (3 : ℕ) ∣ 3 ^ ones (traceWord n j) := dvd_pow_self 3 (by omega)
    rw [← heq] at h3
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right j (by decide)) h3
    omega

/-! ## Target 3: block decomposition with both lengths positive -/

/-- A word that starts odd and ends even decomposes into blocks with *both* components
positive. -/
theorem oddRunCount_blockWord : ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ 0 < p.2) →
    oddRunCount (blockWord L) = L.length
  | [], _ => by simp [blockWord]
  | (q, e) :: L, hpos => by
    obtain ⟨hq, he⟩ := hpos (q, e) (by simp)
    have ih := oddRunCount_blockWord L (fun p hp => hpos p (by simp [hp]))
    simp only [blockWord, List.length_cons]
    rw [oddRunCount_head q e hq he, ih]
    omega

theorem exists_blockWord_oddRunCount_pos (v : List Bool) (hhead : v.head? = some true)
    (hlast : v.getLast? = some false) :
    ∃ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ 0 < p.2) ∧ v = blockWord L ∧
      L.length = oddRunCount v := by
  obtain ⟨L, hL, hword⟩ := exists_blockWord_canonical v hhead hlast
  exact ⟨L, hL, hword, by rw [hword, oddRunCount_blockWord L hL]⟩

/-! ## Target 4: the geometric exponent -/

/-- `log₂ 3`. -/
noncomputable def logTwoThree : ℝ := Real.log 3 / Real.log 2

theorem one_lt_logTwoThree : 1 < logTwoThree := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [logTwoThree, lt_div_iff₀ h2]
  linarith

theorem logTwoThree_lt : logTwoThree < 159 / 100 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : (100 : ℝ) * Real.log 3 < 159 * Real.log 2 := by
    have h : Real.log ((3 : ℝ) ^ (100 : ℕ)) < Real.log ((2 : ℝ) ^ (159 : ℕ)) :=
      Real.log_lt_log (by positivity) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  rw [logTwoThree, div_lt_iff₀ h2]
  linarith

/-- `geomS r = 1 + θ + θ² + … + θ^(r−1)` with `θ = log₂ 3`. -/
noncomputable def geomS : ℕ → ℝ
  | 0 => 0
  | r + 1 => 1 + logTwoThree * geomS r

theorem geomS_nonneg : ∀ r : ℕ, 0 ≤ geomS r
  | 0 => le_refl 0
  | r + 1 => by
    have := geomS_nonneg r
    have h1 := one_lt_logTwoThree
    simp only [geomS]
    nlinarith

theorem geomS_four_le : geomS 4 ≤ 914 / 100 := by
  have h1 := one_lt_logTwoThree
  have h2 := logTwoThree_lt
  simp only [geomS, mul_zero, add_zero]
  nlinarith [sq_nonneg logTwoThree]

theorem geomS_mono : Monotone geomS := by
  have h1 := one_lt_logTwoThree
  have step : ∀ r : ℕ, geomS r ≤ geomS (r + 1) := by
    intro r
    induction r with
    | zero => simp [geomS]
    | succ r ih =>
      simp only [geomS] at ih ⊢
      nlinarith
  exact monotone_nat_of_le_succ step

/-! ## Target 5: the real lower bound on the odd-step count -/

/-- **The run telescoping in `ℝ`.**  Along a block word with all blocks nonempty,
`2^K ≤ (n+1)^(geomS r)`. -/
theorem rpow_two_logTwoThree : (2 : ℝ) ^ logTwoThree = 3 := by
  rw [Real.rpow_def_of_pos (by norm_num), logTwoThree,
    show Real.log 2 * (Real.log 3 / Real.log 2) = Real.log 3 by
      field_simp [(Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'],
    Real.exp_log (by norm_num)]

theorem pow_rpow_logTwoThree (q : ℕ) : ((2 : ℝ) ^ q) ^ logTwoThree = (3 : ℝ) ^ q := by
  rw [← Real.rpow_natCast (2 : ℝ) q, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), rpow_two_logTwoThree, Real.rpow_natCast]

/-- **The step inequality.**  If the head block `(q, e)` (both positive) is traced from `n ≥ 1`
with successor `x'`, then `x' + 1 ≤ (n+1)^logTwoThree`. -/
theorem succ_le_rpow_of_block {n q e : ℕ} (hn : 1 ≤ n) (hq : 0 < q) (he : 0 < e)
    (hword : traceWord n (q + e) = List.replicate q true ++ List.replicate e false) :
    ((tstep^[q + e] n : ℕ) : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ logTwoThree := by
  have hid := segment_identity_of_word hword
  set x := tstep^[q + e] n with hx
  -- `2^q ∣ n + 1`
  have hdvd : (2 : ℕ) ^ q ∣ n + 1 := by
    have h1 : (2 : ℕ) ^ q ∣ 3 ^ q * (n + 1) := by
      rw [← hid]
      exact Nat.dvd_add (Dvd.dvd.mul_right (pow_dvd_pow 2 (Nat.le_add_right q e)) _) dvd_rfl
    exact (Nat.Coprime.pow _ _ (by decide)).dvd_of_dvd_mul_left h1
  have hAnat : (2 : ℕ) ^ q ≤ n + 1 := Nat.le_of_dvd (by omega) hdvd
  have hnatb : 2 ^ (q + 1) * x ≤ 3 ^ q * (n + 1) := by
    calc 2 ^ (q + 1) * x ≤ 2 ^ (q + e) * x :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ ≤ 3 ^ q * (n + 1) := by omega
  set N : ℝ := (n : ℝ) + 1 with hN
  set A : ℝ := (2 : ℝ) ^ q with hA
  have hApos : 0 < A := by positivity
  have hNpos : 0 < N := by rw [hN]; positivity
  have hN2 : (2 : ℝ) ≤ N := by
    rw [hN]; have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hθ := one_lt_logTwoThree
  have hA_le : A ≤ N := by
    rw [hA, hN]; exact_mod_cast hAnat
  have hb : 2 * A * (x : ℝ) ≤ (3 : ℝ) ^ q * N := by
    have := hnatb
    have hc : ((2 ^ (q + 1) * x : ℕ) : ℝ) ≤ ((3 ^ q * (n + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hc
    rw [pow_succ] at hc
    rw [hA, hN]; push_cast; linarith [hc]
  -- `3^q / A ≤ N^(θ-1)`
  have hsub : A ^ (logTwoThree - 1) = (3 : ℝ) ^ q / A := by
    rw [Real.rpow_sub hApos, pow_rpow_logTwoThree, Real.rpow_one]
  have hC : (3 : ℝ) ^ q / A ≤ N ^ (logTwoThree - 1) := by
    rw [← hsub]; exact Real.rpow_le_rpow hApos.le hA_le (by linarith)
  have hNθ : N ^ (logTwoThree - 1) * N = N ^ logTwoThree := by
    have h := (Real.rpow_add hNpos (logTwoThree - 1) 1).symm
    simpa using h
  have hxle : (x : ℝ) ≤ N ^ logTwoThree / 2 := by
    have h1 : 2 * (x : ℝ) ≤ ((3 : ℝ) ^ q / A) * N := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hApos]; nlinarith
    have h2 : ((3 : ℝ) ^ q / A) * N ≤ N ^ (logTwoThree - 1) * N :=
      mul_le_mul_of_nonneg_right hC hNpos.le
    rw [hNθ] at h2
    linarith
  have hge2 : (2 : ℝ) ≤ N ^ logTwoThree := by
    calc (2 : ℝ) ≤ N := hN2
      _ = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ logTwoThree := Real.rpow_le_rpow_of_exponent_le (by linarith) hθ.le
  linarith

/-- **The run telescoping in `ℝ`.**  Along a block word with all blocks nonempty,
`2^K ≤ (n+1)^(geomS r)`. -/
theorem two_pow_ones_le_rpow : ∀ (L : List (ℕ × ℕ)) (n : ℕ), 1 ≤ n →
    (∀ p ∈ L, 0 < p.1 ∧ 0 < p.2) → traceWord n (blockWord L).length = blockWord L →
    (2 : ℝ) ^ ones (blockWord L) ≤ ((n : ℝ) + 1) ^ geomS L.length
  | [], n, _, _, _ => by simp [blockWord, ones, geomS, Real.rpow_zero]
  | (q, e) :: L, n, hn, hpos, hword => by
    obtain ⟨hq, he⟩ := hpos (q, e) (by simp)
    have hlen := blockWord_cons_length q e L
    have hsplit : traceWord n (q + e) ++ traceWord (tstep^[q + e] n) (blockWord L).length =
        (List.replicate q true ++ List.replicate e false) ++ blockWord L := by
      rw [← traceWord_add, ← hlen, hword]; rfl
    obtain ⟨hhead, htail⟩ := List.append_inj hsplit (by simp)
    set x := tstep^[q + e] n with hx
    have hx1 : 1 ≤ x := tstep_iterate_pos hn (q + e)
    have ih := two_pow_ones_le_rpow L x hx1 (fun p hp => hpos p (by simp [hp])) htail
    have hstep := succ_le_rpow_of_block hn hq he hhead
    have hones : ones (blockWord ((q, e) :: L)) = q + ones (blockWord L) := by
      simp only [blockWord, ones_append]; simp
    set N : ℝ := (n : ℝ) + 1 with hN
    have hNpos : 0 < N := by rw [hN]; positivity
    have hg := geomS_nonneg L.length
    -- transport the induction hypothesis along `x + 1 ≤ N^θ`
    have hchain : ((x : ℝ) + 1) ^ geomS L.length ≤ N ^ (logTwoThree * geomS L.length) := by
      calc ((x : ℝ) + 1) ^ geomS L.length ≤ (N ^ logTwoThree) ^ geomS L.length :=
            Real.rpow_le_rpow (by positivity) hstep hg
        _ = N ^ (logTwoThree * geomS L.length) := (Real.rpow_mul hNpos.le _ _).symm
    have hAnat : ((2 : ℝ) ^ q) ≤ N := by
      have hdvd : (2 : ℕ) ^ q ∣ n + 1 := by
        have hid := segment_identity_of_word hhead
        have h1 : (2 : ℕ) ^ q ∣ 3 ^ q * (n + 1) := by
          rw [← hid]
          exact Nat.dvd_add (Dvd.dvd.mul_right (pow_dvd_pow 2 (Nat.le_add_right q e)) _) dvd_rfl
        exact (Nat.Coprime.pow _ _ (by decide)).dvd_of_dvd_mul_left h1
      have := Nat.le_of_dvd (by omega) hdvd
      rw [hN]; exact_mod_cast this
    rw [hones, pow_add]
    calc (2 : ℝ) ^ q * 2 ^ ones (blockWord L)
        ≤ N * N ^ (logTwoThree * geomS L.length) :=
          mul_le_mul hAnat (le_trans ih hchain) (by positivity) hNpos.le
      _ = N ^ (1 + logTwoThree * geomS L.length) := by
          rw [Real.rpow_add hNpos, Real.rpow_one]
      _ = N ^ geomS ((q, e) :: L).length := by simp [geomS]

/-! ## Target 6: the upper side -/

/-- `(n+1)^r − n^r ≤ 15 n^(r−1)` for `1 ≤ r ≤ 4`. -/
theorem succ_pow_sub_le {n r : ℕ} (hn : 1 ≤ n) (h1 : 1 ≤ r) (h4 : r ≤ 4) :
    (n + 1) ^ r - n ^ r ≤ 15 * n ^ (r - 1) := by
  have hnn : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hn3 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ (by omega)
  interval_cases r <;>
    refine Nat.sub_le_iff_le_add.mpr ?_ <;> ring_nf <;> nlinarith [hn, hnn, hn3]

/-- With at most four odd runs, the Simons–de Weger bound reads `D · n ≤ 15 · 3^K`. -/
theorem gap_mul_le_fifteen {n m : ℕ} (hn : n % 2 = 1) (h : At n m) (hsurv : n ≤ tstep^[m] n)
    (hr : oddRunCount (traceWord n m) ≤ 4) :
    (2 ^ m - 3 ^ ones (traceWord n m)) * n ≤ 15 * 3 ^ ones (traceWord n m) := by
  have hn1 : 1 ≤ n := by omega
  have hb := gap_mul_pow_le hn h hsurv
  set K := ones (traceWord n m) with hKdef
  set r := oddRunCount (traceWord n m) with hrdef
  set D := 2 ^ m - 3 ^ K with hD
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · have hD0 : D = 0 := by rw [hr0] at hb; simpa using hb
    rw [hD0]; simp
  · have hexp : (n + 1) ^ r - n ^ r ≤ 15 * n ^ (r - 1) := succ_pow_sub_le hn1 hr1 hr
    have hsplit : n ^ r = n * n ^ (r - 1) := by
      conv_lhs => rw [show r = 1 + (r - 1) by omega]
      rw [pow_add, pow_one]
    have hchain : (D * n) * n ^ (r - 1) ≤ (15 * 3 ^ K) * n ^ (r - 1) := by
      calc (D * n) * n ^ (r - 1) = D * n ^ r := by rw [hsplit]; ring
        _ ≤ 3 ^ K * ((n + 1) ^ r - n ^ r) := hb
        _ ≤ 3 ^ K * (15 * n ^ (r - 1)) := Nat.mul_le_mul_left _ hexp
        _ = (15 * 3 ^ K) * n ^ (r - 1) := by ring
    exact Nat.le_of_mul_le_mul_right hchain (by positivity)

/-! ## Target 7: stopping-time correctness on few-run crossings -/

theorem descends_of_oddRunCount_le_four (hv : CSTVerified) {n m : ℕ} (hn : 2 ≤ n)
    (h : At n m) (hr : oddRunCount (traceWord n m) ≤ 4) : tstep^[m] n < n := by
  sorry

end CollatzMoonshot.FrontA.FirstCrossing
