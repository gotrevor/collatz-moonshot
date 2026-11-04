/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitTimeLawChain

/-!
# The time law

Tao's `tao_collatz` says that almost every start in logarithmic density gets below `f n`, for any
`f → ∞`, and carries no time.  Here is the time: `(1 / β + o(1)) size n` steps of `tstep`, with
`β = 1 − log₂ 3 / 2` (`timeLaw_upper`), and for slowly growing `f` no sooner (`timeLaw_lower`).

This is the stochastic model's total stopping time `C* size n`, as far as `f → ∞` reaches.  It says
nothing about reaching `1`.

`experiments/conjugacy/time_law.py` compares it with data out to `k = 20000`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-! ## The leaves -/

/-- **The stage events at a rate.**  For a start drawn from `winLaw x`, the start event at `x` and
the location events at `x_j`, `j < J`, all hold except with probability `M log(X)^(−κ)`, as long
as every scale `x_j`, `j ≤ J`, is at least `X ≥ X₀`.  The exponent `κ ≤ c_stab` comes from
Proposition 1.11 along the chain, and the sum over the scales is geometric, dominated by the last. -/
theorem chainFail_prob_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 1000) :
    ∃ κ M X₀ : ℝ, 0 < κ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ (x : ℝ) (J : ℕ), (∀ j ≤ J, X ≤ scale x j) →
      (winLaw x).expect (Set.indicator {n | ¬ (ScaleGood [true] (1 / 100) η x n ∧
        ∀ j < J, LocGood [true] (1 / 100) η (scale x j) (passLoc ⌊scale x j⌋₊ n))} 1) ≤
        M * Real.log X ^ (-κ) := by
  sorry

/-- **The time along the chain.**  An odd start `m ∈ [x^α, x^(α²)]` on the height line through
`τ size m`, whose stage events hold along `J` scales, all of them large, is below `x_J` within
`(1 / β + ε) size m` steps: the height line takes it below `m^θ` in about `(1 − θ / 2) size m / β`
steps, a run of halvings at most `θ size m` reaches the passage below the first scale under it,
and the remaining stages take at most `lam x_j ≤ log₂ x_j / 20` letters each, `≤ 52 θ size m` in
all. -/
theorem reach_of_chain {ε : ℝ} (hε : 0 < ε) :
    ∃ δ τ X₀ : ℝ, 0 < δ ∧ 0 < τ ∧ τ * heightSlope < 1 ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 1000 →
      ∀ (x : ℝ) (J : ℕ), (∀ j ≤ J, X₀ ≤ scale x j) → ∀ m : ℕ, m % 2 = 1 → x ^ alpha ≤ m →
        (m : ℝ) ≤ x ^ alpha ^ 2 → GoodOddUpTo δ τ m → ScaleGood [true] (1 / 100) η x m →
        (∀ j < J, LocGood [true] (1 / 100) η (scale x j) (passLoc ⌊scale x j⌋₊ m)) →
        ∃ t : ℕ, (t : ℝ) ≤ (1 / heightSlope + ε) * Nat.size m ∧ (tstep^[t] m : ℝ) ≤ scale x J :=
  reach_of_chain_holds hε

/-- **The last scale above `X`.**  For `1 < X ≤ x` there is `J` with every `x_j ≥ X`, `j ≤ J`,
and `x_J ≤ X^α`. -/
theorem exists_last_scale {X x : ℝ} (hX : 1 < X) (hx : X ≤ x) :
    ∃ J : ℕ, (∀ j ≤ J, X ≤ scale x j) ∧ scale x J ≤ X ^ alpha := by
  classical
  have hx0 : 0 < x := by linarith
  have hlX : 0 < Real.log X := Real.log_pos hX
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hex : ∃ j : ℕ, scale x (j + 1) < X := by
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos hlX hlx)
      (show alpha⁻¹ < 1 by rw [alpha_eq]; norm_num)
    refine ⟨j, ?_⟩
    have hj' : alpha⁻¹ ^ (j + 1) * Real.log x < Real.log X := by
      rw [lt_div_iff₀ hlx] at hj
      have : alpha⁻¹ ^ (j + 1) ≤ alpha⁻¹ ^ j :=
        pow_le_pow_of_le_one (by rw [alpha_eq]; norm_num) (by rw [alpha_eq]; norm_num) (by omega)
      nlinarith
    rw [scale, Real.rpow_def_of_pos hx0, ← Real.lt_log_iff_exp_lt (by linarith)]
    linarith
  refine ⟨Nat.find hex, fun j hj => ?_, ?_⟩
  · rcases j with _ | i
    · simpa [scale] using hx
    · exact not_lt.mp (Nat.find_min hex (show i < Nat.find hex by omega))
  · rw [← scale_succ_rpow hx0.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) (Nat.find_spec hex).le
      (by norm_num [alpha])

/-- A minorant tending to infinity: `g m ≤ f n` for `m ≤ n`. -/
theorem exists_minorant {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    ∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ ∀ m n, m ≤ n → g m ≤ f n := by
  obtain ⟨b, hb⟩ := bddBelow_range_of_tendsto_atTop_atTop hf
  have hne : ∀ m : ℕ, Nonempty {n : ℕ // m ≤ n} := fun m => ⟨⟨m, le_rfl⟩⟩
  have hbdd : ∀ m : ℕ, BddBelow (Set.range fun n : {n : ℕ // m ≤ n} => f n) := fun m =>
    ⟨b, by rintro _ ⟨n, rfl⟩; exact hb ⟨n, rfl⟩⟩
  refine ⟨fun m => ⨅ n : {n : ℕ // m ≤ n}, f n, ?_, fun m n hmn => ciInf_le (hbdd m) ⟨n, hmn⟩⟩
  rw [tendsto_atTop]
  intro C
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hf.eventually_ge_atTop C)
  filter_upwards [eventually_ge_atTop N] with m hm
  haveI := hne m
  exact le_ciInf fun n => hN n (le_trans hm n.2)

/-! ## Assembly -/

/-- **The time law on a window.**  Under `winLaw x`, the start gets below `g m` within
`(1 / β + ε) size m` steps with probability tending to `1`.  For each large `X`, the chain down to
the last scale above `X` fails with probability at most `M log(X)^(−κ)`, and `x_J ≤ X^α ≤ g m`
once `x` is large. -/
theorem timeLaw_odd_window {g : ℕ → ℝ} (hg : Tendsto g atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x => (winLaw x).expect (Set.indicator {m | ¬ ∃ t : ℕ,
      (t : ℝ) ≤ (1 / heightSlope + ε) * Nat.size m ∧ (tstep^[t] m : ℝ) ≤ g m} 1)) atTop
      (𝓝 0) := by
  obtain ⟨δ, τ, X₁, hδ, hτ0, hτ, hreach⟩ := reach_of_chain hε
  obtain ⟨κ, M, X₂, hκ, hchain⟩ := chainFail_prob_le (η := 1 / 1000) (by norm_num) le_rfl
  have hgood := goodOddUpTo_whp hτ0 hτ hδ
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun x =>
    lt_of_lt_of_le ha (prob_nonneg _ _), fun a ha => ?_⟩
  -- the scale `X` of the last stage
  have hrate : Tendsto (fun X : ℝ => M * Real.log X ^ (-κ)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hκ).comp Real.tendsto_log_atTop).const_mul M
    simpa using this
  obtain ⟨X, hXa, hX⟩ := ((hrate.eventually (gt_mem_nhds (half_pos ha))).and
    (eventually_ge_atTop (max (max X₁ X₂) 2))).exists
  have hX1 : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3 : 1 < X := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hX)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hg.eventually_ge_atTop (X ^ alpha))
  have hxa : Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop (by norm_num [alpha])
  filter_upwards [hgood.eventually (gt_mem_nhds (half_pos ha)), eventually_ge_atTop X,
    eventually_ge_atTop X_windowBase, hxa.eventually_ge_atTop (N : ℝ)] with x hxg hxX hxw hxN
  obtain ⟨J, hJX, hJ⟩ := exists_last_scale hX3 hxX
  have hfail := hchain X hX2 x J hJX
  refine lt_of_le_of_lt (le_trans (prob_mono_support _ (B := {n | ¬ GoodOddUpTo δ τ n} ∪
    {n | ¬ (ScaleGood [true] (1 / 100) (1 / 1000) x n ∧ ∀ j < J,
      LocGood [true] (1 / 100) (1 / 1000) (scale x j) (passLoc ⌊scale x j⌋₊ n))})
    fun m hm hbad => ?_) (expect_indicator_union_le _ _ _)) (by linarith)
  obtain ⟨hodd, hlo, hhi⟩ := winLaw_support hxw hm
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
  obtain ⟨hG, hS, hL⟩ := hcon
  obtain ⟨t, ht, htx⟩ := hreach (1 / 1000) (by norm_num) (by norm_num) x J
    (fun j hj => le_trans hX1 (hJX j hj)) m hodd hlo hhi hG hS hL
  have hmN : N ≤ m := by exact_mod_cast le_trans hxN hlo
  exact hbad ⟨t, ht, le_trans htx (le_trans hJ (hN m hmN))⟩

/-- **Within `(1 / β + ε) size n` steps the orbit is below `f n`.**  The chain over a number of scales
growing with `x`, down to a large constant `X`, with exceptions summing to `g X → 0`.  Believed, 85%. -/
theorem timeLaw_upper {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    LogDens0 fun n : ℕ =>
      ¬ ∃ t : ℕ, (t : ℝ) ≤ (1 / heightSlope + ε) * Nat.size n ∧ (tstep^[t] n : ℝ) ≤ f n := by
  obtain ⟨g, hg, hgf⟩ := exists_minorant hf
  have hodd := logDens0OfWindow _ (timeLaw_odd_window hg hε)
  refine ((logDens0OddPart _ hodd).or (logDens0_of_bdd (B := 0) fun n (h : n = 0) => h.le)).mono
    fun n hn => ?_
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨⟨t, ht, htg⟩, hn0⟩ := hcon
  apply hn
  have hβ := heightSlope_pos
  have hβ5 := heightSlope_le
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hm1 : 1 ≤ oddPart n := by have := oddPart_odd hnpos; omega
  have hnm : 2 ^ padicValNat 2 n * oddPart n = n := two_pow_mul_oddPart n
  have hmn : oddPart n ≤ n := by
    conv_rhs => rw [← hnm]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hsize : Nat.size n = Nat.size (oddPart n) + padicValNat 2 n := by
    conv_lhs => rw [← hnm]
    exact size_two_pow_mul (by omega) _
  refine ⟨t + padicValNat 2 n, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ 1 / heightSlope + ε := by
      have : (1 : ℝ) ≤ 1 / heightSlope := by
        rw [le_div_iff₀ hβ]
        linarith
      linarith
    have ha : (0 : ℝ) ≤ padicValNat 2 n := Nat.cast_nonneg _
    rw [hsize]
    push_cast
    nlinarith
  · have hT : tstep^[padicValNat 2 n] n = oddPart n := by
      have := tstep_iterate_two_pow_mul (padicValNat 2 n) (oddPart n)
      rwa [hnm] at this
    rw [Function.iterate_add_apply, hT]
    exact le_trans htg (hgf _ _ hmn)

/-- **For `f` below every power of `n`, not within `(1 / β − ε) size n` steps.**  From
`firstPassage_sharp` at `θ = min (1 / 2) (β ε / 2)`, since `1 / β − ε ≤ (1 − θ) / β − ε / 2`; the
starts with `f n > n^θ` are bounded. -/
theorem timeLaw_lower {f : ℕ → ℝ} (hf : ∀ θ : ℝ, 0 < θ → ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ θ)
    {ε : ℝ} (hε : 0 < ε) :
    LogDens0 fun n : ℕ =>
      ∃ t : ℕ, (t : ℝ) ≤ (1 / heightSlope - ε) * Nat.size n ∧ (tstep^[t] n : ℝ) ≤ f n := by
  have hβ := heightSlope_pos
  set θ : ℝ := min (1 / 2) (heightSlope * ε / 2) with hθdef
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hθε : θ / heightSlope ≤ ε / 2 := by
    rw [div_le_iff₀ hβ]
    have := min_le_right (1 / 2 : ℝ) (heightSlope * ε / 2)
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hf θ hθ)
  refine ((firstPassage_sharp hθ hθ1 (half_pos hε)).or
    (logDens0_of_bdd (B := N) fun n (h : ¬ f n ≤ (n : ℝ) ^ θ) => ?_)).mono fun n hn => ?_
  · by_contra hlt
    exact h (hN n (not_le.mp hlt).le)
  · obtain ⟨t, ht, hft⟩ := hn
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨⟨hfirst, -⟩, hfn⟩ := hcon
    have hsn : (0 : ℝ) ≤ Nat.size n := Nat.cast_nonneg _
    have hc : 1 / heightSlope - ε ≤ (1 - θ) / heightSlope - ε / 2 := by
      have : (1 - θ) / heightSlope = 1 / heightSlope - θ / heightSlope := by ring
      linarith
    have := hfirst t (le_trans ht (mul_le_mul_of_nonneg_right hc hsn))
    linarith

end CollatzMoonshot.Conjugacy
