/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.ChampernowneThreshold

/-!
# `𝒞_C` is not normal for `C ≥ 5`, unconditionally

`not_normal_of_earlyArrival` assumes that a positive density of starts reach `1` early.  Normality
supplies that itself.

Heights stay `≥ 1`, so the drift of an orbit is bounded below: an even letter halves the height, an
odd letter at height `> 100` multiplies it by at most `2^0.59`, and an odd letter at height `≤ 100`
by at most `2`.  So a word of `C s` letters of an `s`-bit start has `E ≤ s + 0.59 H + B`
(`evenCount_le`), with `E` even letters, `H` odd letters above height `100`, `B` odd letters at or
below it.  Every start at or below `100` reaches `1` within `75` steps (`exists_iterate_eq_one`), and
then alternates, so `B` is at most `75` more than the number of visits to `1`
(`lowOdd_le_oneCount_add`), each of which starts a block `(10)^4` unless it is within `8` of the end.

Summed over the first `N` words, with `P` letters, `O` odd letters and `A` interior `(10)^4` blocks,
this reads `P − O ≤ P / 5 + 0.59 O + 0.41 (A + 83 N)` for every `C ≥ 5` (`drift_total`), with no
hypothesis.  If `𝒞_C` were normal then `O / P → 1/2`, `A / P ≤ 2^(−8) + o(1)`, `N / P → 0`, and the
limit reads `0.5 ≤ 0.2 + 0.295 + 0.41 · 2^(−8) = 0.4966`.

`experiments/conjugacy/drift_check.py` checks the per-word inequality on `n < 2^16`, with no
violations, and shows it failing for the coefficient `0.5` in place of `0.59`.  At `C = 4` the margin
`1/2 − 1/C − 0.295` is negative, so the argument stops, as it must.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- Even letters among the first `t` of `n`. -/
def evenCount (n t : ℕ) : ℕ := ((Finset.range t).filter fun i => tstep^[i] n % 2 = 0).card

/-- Odd letters among the first `t` of `n`, at height above `100`. -/
def highOdd (n t : ℕ) : ℕ :=
  ((Finset.range t).filter fun i => tstep^[i] n % 2 = 1 ∧ 100 < tstep^[i] n).card

/-- Odd letters among the first `t` of `n`, at height at most `100`. -/
def lowOdd (n t : ℕ) : ℕ :=
  ((Finset.range t).filter fun i => tstep^[i] n % 2 = 1 ∧ tstep^[i] n ≤ 100).card

/-- Visits to `1` among the first `t` steps of `n`. -/
def oneCount (n t : ℕ) : ℕ := ((Finset.range t).filter fun i => tstep^[i] n = 1).card

theorem evenCount_add_highOdd_add_lowOdd (n t : ℕ) :
    evenCount n t + highOdd n t + lowOdd n t = t := by
  simp only [evenCount, highOdd, lowOdd, Finset.card_filter, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (g := fun _ => 1) ?_]
  · simp
  · intro i _
    split_ifs <;> omega

/-- The real inequality behind the coefficient: above height `100` an odd step multiplies by at most
`2^0.59`. -/
theorem logb_tstep_odd_high_le {y : ℕ} (hodd : y % 2 = 1) (hy : 100 < y) :
    Real.logb 2 (tstep y) ≤ Real.logb 2 y + 0.59 := by
  have h2 : 2 * tstep y = 3 * y + 1 := by
    have : tstep y = (3 * y + 1) / 2 := by simp [tstep, hodd]
    omega
  have h2R : (2 : ℝ) * (tstep y : ℝ) = 3 * (y : ℝ) + 1 := by exact_mod_cast h2
  have hyR : (101 : ℝ) ≤ y := by exact_mod_cast hy
  have hT0 : (0 : ℝ) < tstep y := by linarith
  have hle : (tstep y : ℝ) ≤ 1.505 * (y : ℝ) := by linarith
  have hc : Real.logb 2 1.505 ≤ 0.59 := by
    have h1 : Real.logb 2 ((1.505 : ℝ) ^ 100) ≤ Real.logb 2 ((2 : ℝ) ^ 59) :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h1
    norm_num at h1 ⊢
    linarith
  have hy0 : (y : ℝ) ≠ 0 := by intro h; rw [h] at hyR; norm_num at hyR
  calc Real.logb 2 (tstep y) ≤ Real.logb 2 (1.505 * (y : ℝ)) :=
        Real.logb_le_logb_of_le (by norm_num) hT0 hle
    _ = Real.logb 2 1.505 + Real.logb 2 y := Real.logb_mul (by norm_num) hy0
    _ ≤ Real.logb 2 y + 0.59 := by linarith

/-- At any height `≥ 1` an odd step at most doubles. -/
theorem logb_tstep_odd_le {y : ℕ} (hodd : y % 2 = 1) :
    Real.logb 2 (tstep y) ≤ Real.logb 2 y + 1 := by
  have h2 : 2 * tstep y = 3 * y + 1 := by
    have : tstep y = (3 * y + 1) / 2 := by simp [tstep, hodd]
    omega
  have h2R : (2 : ℝ) * (tstep y : ℝ) = 3 * (y : ℝ) + 1 := by exact_mod_cast h2
  have hyN : 1 ≤ y := by omega
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hyN
  have hT0 : (0 : ℝ) < tstep y := by linarith
  calc Real.logb 2 (tstep y) ≤ Real.logb 2 (2 * (y : ℝ)) :=
        Real.logb_le_logb_of_le (by norm_num) hT0 (by linarith)
    _ = Real.logb 2 2 + Real.logb 2 y := Real.logb_mul (by norm_num) (by linarith)
    _ = Real.logb 2 y + 1 := by rw [Real.logb_self_eq_one (by norm_num)]; ring

/-- An even step at height `≥ 1` halves. -/
theorem logb_tstep_even_eq {y : ℕ} (heven : y % 2 = 0) (hy : 1 ≤ y) :
    Real.logb 2 (tstep y) = Real.logb 2 y - 1 := by
  have h2 : y = 2 * tstep y := by
    have : tstep y = y / 2 := by simp [tstep, heven]
    omega
  have hT : 1 ≤ tstep y := by omega
  have hT0 : (tstep y : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ tstep y := by exact_mod_cast hT
    linarith
  have hyR : (y : ℝ) = 2 * (tstep y : ℝ) := by exact_mod_cast h2
  rw [hyR, Real.logb_mul (by norm_num) hT0, Real.logb_self_eq_one (by norm_num)]
  ring

/-- One step keeps a height `≥ 1`. -/
theorem one_le_tstep {y : ℕ} (hy : 1 ≤ y) : 1 ≤ tstep y := by
  unfold tstep
  split_ifs <;> omega

/-- Heights stay `≥ 1`. -/
theorem one_le_tstep_iterate {n : ℕ} (hn : 1 ≤ n) (t : ℕ) : 1 ≤ tstep^[t] n := by
  induction t with
  | zero => simpa using hn
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact one_le_tstep ih

/-- One more letter, even count. -/
theorem evenCount_succ (n t : ℕ) :
    evenCount n (t + 1) = evenCount n t + if tstep^[t] n % 2 = 0 then 1 else 0 := by
  simp only [evenCount, Finset.card_filter, Finset.sum_range_succ]

/-- One more letter, high odd count. -/
theorem highOdd_succ (n t : ℕ) :
    highOdd n (t + 1) = highOdd n t + if tstep^[t] n % 2 = 1 ∧ 100 < tstep^[t] n then 1 else 0 := by
  simp only [highOdd, Finset.card_filter, Finset.sum_range_succ]

/-- One more letter, low odd count. -/
theorem lowOdd_succ (n t : ℕ) :
    lowOdd n (t + 1) = lowOdd n t + if tstep^[t] n % 2 = 1 ∧ tstep^[t] n ≤ 100 then 1 else 0 := by
  simp only [lowOdd, Finset.card_filter, Finset.sum_range_succ]

/-- The height at time `t` in terms of the three letter counts. -/
theorem logb_iterate_le {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    Real.logb 2 (tstep^[t] n : ℝ) ≤
      Real.logb 2 n - evenCount n t + 0.59 * highOdd n t + lowOdd n t := by
  induction t with
  | zero => simp [evenCount, highOdd, lowOdd]
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have hy := one_le_tstep_iterate hn t
    rw [evenCount_succ, highOdd_succ, lowOdd_succ]
    generalize tstep^[t] n = y at *
    by_cases he : y % 2 = 0
    · rw [if_pos he, if_neg (by omega), if_neg (by omega), logb_tstep_even_eq he hy]
      push_cast
      linarith
    · have ho : y % 2 = 1 := by omega
      by_cases hh : 100 < y
      · rw [if_neg he, if_pos ⟨ho, hh⟩, if_neg (by omega)]
        have := logb_tstep_odd_high_le ho hh
        push_cast
        linarith
      · rw [if_neg he, if_neg (by omega), if_pos ⟨ho, by omega⟩]
        have := logb_tstep_odd_le ho
        push_cast
        linarith

/-- **Drift, per word.**  The height at time `t` is at least `1`. -/
theorem evenCount_le {n s : ℕ} (hn : 1 ≤ n) (hs : n < 2 ^ s) (t : ℕ) :
    (evenCount n t : ℝ) ≤ s + 0.59 * highOdd n t + lowOdd n t := by
  have h := logb_iterate_le hn t
  have h0 : 0 ≤ Real.logb 2 (tstep^[t] n : ℝ) := by
    apply Real.logb_nonneg (by norm_num)
    exact_mod_cast one_le_tstep_iterate hn t
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (n : ℝ) ≤ (2 : ℝ) ^ s := by exact_mod_cast hs.le
  have hlog : Real.logb 2 (n : ℝ) ≤ s := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hnR hsR
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
  linarith

/-- Every start at or below `100` reaches `1` within `75` steps. -/
theorem exists_iterate_eq_one : ∀ y ∈ Finset.Icc 1 100, ∃ j ≤ 75, tstep^[j] y = 1 := by
  decide +kernel

/-- From a hit of `1` on, the orbit alternates `1, 2, 1, 2, …`. -/
theorem iterate_add_of_eq_one {n a : ℕ} (h : tstep^[a] n = 1) (i : ℕ) :
    tstep^[a + i] n = if i % 2 = 0 then 1 else 2 := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    rw [← add_assoc, Function.iterate_succ_apply', ih]
    by_cases hi : i % 2 = 0
    · have : (i + 1) % 2 ≠ 0 := by omega
      simp [hi, this, tstep]
    · have : (i + 1) % 2 = 0 := by omega
      simp [hi, this, tstep]

/-- Low odd letters other than `1` all fall within `75` steps of the first one. -/
theorem lowOdd_le_oneCount_add {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    lowOdd n t ≤ oneCount n t + 75 := by
  classical
  set R := (Finset.range t).filter
    (fun i => tstep^[i] n % 2 = 1 ∧ tstep^[i] n ≤ 100 ∧ tstep^[i] n ≠ 1) with hR
  have hsplit : lowOdd n t ≤ oneCount n t + R.card := by
    unfold lowOdd oneCount
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range, hR] at hi ⊢
    by_cases h1 : tstep^[i] n = 1
    · exact Or.inl ⟨hi.1, h1⟩
    · exact Or.inr ⟨hi.1, hi.2.1, hi.2.2, h1⟩
  have hRcard : R.card ≤ 75 := by
    rcases R.eq_empty_or_nonempty with he | hne
    · simp [he]
    · have hmem := Finset.min'_mem R hne
      set i₀ := R.min' hne with hi₀
      simp only [hR, Finset.mem_filter] at hmem
      obtain ⟨j, hj, hit⟩ := exists_iterate_eq_one (tstep^[i₀] n)
        (Finset.mem_Icc.mpr ⟨one_le_tstep_iterate hn i₀, hmem.2.2.1⟩)
      rw [← Function.iterate_add_apply] at hit
      have hsub : R ⊆ Finset.Ico i₀ (j + i₀) := by
        intro i hi
        have hle : i₀ ≤ i := Finset.min'_le R i hi
        simp only [hR, Finset.mem_filter] at hi
        rw [Finset.mem_Ico]
        refine ⟨hle, ?_⟩
        by_contra hge
        obtain ⟨k, rfl⟩ : ∃ k, i = j + i₀ + k := ⟨i - (j + i₀), by omega⟩
        have hv := iterate_add_of_eq_one hit k
        have ⟨_, hodd, _, hne1⟩ := hi
        rw [hv] at hodd hne1
        split_ifs at hodd hne1; omega
      have := Finset.card_le_card hsub
      rw [Nat.card_Ico] at this
      omega
  omega

/-- A visit to `1` starts a block `(10)^m` unless it is within `2m` of the end. -/
theorem oneCount_le_window_add (n t m : ℕ) :
    oneCount n t ≤ ((Finset.range t).filter fun i => i + (altWord m).length ≤ t ∧
      WindowMatch (fun s => (altWord m).getD s false) (altWord m).length i n).card + 2 * m := by
  classical
  have hsub : (Finset.range t).filter (fun i => tstep^[i] n = 1) ⊆
      ((Finset.range t).filter fun i => i + (altWord m).length ≤ t ∧
        WindowMatch (fun s => (altWord m).getD s false) (altWord m).length i n) ∪
      Finset.Ico (t - 2 * m) t := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    by_cases hfit : i + (altWord m).length ≤ t
    · refine Or.inl ⟨hi.1, hfit, ?_⟩
      have hw := windowMatch_altWord hi.2 m 0
      rwa [Nat.mul_zero, Nat.add_zero] at hw
    · rw [length_altWord] at hfit
      exact Or.inr ⟨by omega, hi.1⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Nat.card_Ico] at hc
  unfold oneCount
  omega

/-- Odd letters are the interior occurrences of the one-letter word `1`. -/
theorem interior_true_eq (C N : ℕ) :
    interior C (fun s => [true].getD s false) [true].length N =
      ∑ n ∈ Finset.range N, (highOdd (n + 1) (champLen C n) + lowOdd (n + 1) (champLen C n)) := by
  unfold interior
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [highOdd, lowOdd, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have key : (i + [true].length ≤ champLen C n ∧
      WindowMatch (fun s => [true].getD s false) [true].length i (n + 1)) ↔
      tstep^[i] (n + 1) % 2 = 1 := by
    constructor
    · rintro ⟨_, hw⟩
      have := hw 0 (by simp)
      simpa [accWord] using this
    · intro hodd
      refine ⟨by simpa using hi', fun s hs => ?_⟩
      have hs0 : s = 0 := by simpa using hs
      subst hs0
      simpa [accWord] using hodd
  by_cases hodd : tstep^[i] (n + 1) % 2 = 1
  · rw [if_pos (key.2 hodd)]
    split_ifs <;> omega
  · rw [if_neg (fun h => hodd (key.1 h))]
    split_ifs <;> omega

/-- `P = C ∑ size` for `C ≥ 1`. -/
theorem cum_eq_mul_sum_size (C : ℕ) (hC : 1 ≤ C) (N : ℕ) :
    cum (champLen C) N = C * ∑ n ∈ Finset.range N, Nat.size (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [cum_succ, Finset.sum_range_succ, ih, champLen, max_eq_left hC, mul_add]

/-- One word's share of `drift_total`. -/
theorem word_drift (C : ℕ) (hC : 1 ≤ C) (n : ℕ) :
    (C : ℝ) * (Nat.size (n + 1) : ℝ) -
        ((highOdd (n + 1) (champLen C n) : ℝ) + lowOdd (n + 1) (champLen C n)) ≤
      (Nat.size (n + 1) : ℝ) +
        0.59 * ((highOdd (n + 1) (champLen C n) : ℝ) + lowOdd (n + 1) (champLen C n)) +
        0.41 * (((((Finset.range (champLen C n)).filter
          fun i => i + (altWord 4).length ≤ champLen C n ∧
            WindowMatch (fun s => (altWord 4).getD s false) (altWord 4).length i
              (n + 1)).card : ℕ) : ℝ) + 83) := by
  have hlen : champLen C n = C * Nat.size (n + 1) := by rw [champLen, max_eq_left hC]
  have hE := evenCount_le (n := n + 1) (s := Nat.size (n + 1)) (by omega)
    (Nat.lt_size_self (n + 1)) (champLen C n)
  have hpart := evenCount_add_highOdd_add_lowOdd (n + 1) (champLen C n)
  have hlow := lowOdd_le_oneCount_add (n := n + 1) (by omega) (champLen C n)
  have hone := oneCount_le_window_add (n + 1) (champLen C n) 4
  have hpartR : (evenCount (n + 1) (champLen C n) : ℝ) + highOdd (n + 1) (champLen C n) +
      lowOdd (n + 1) (champLen C n) = (C : ℝ) * (Nat.size (n + 1) : ℝ) := by
    have : (evenCount (n + 1) (champLen C n) + highOdd (n + 1) (champLen C n) +
      lowOdd (n + 1) (champLen C n) : ℕ) = C * Nat.size (n + 1) := by rw [hpart, hlen]
    exact_mod_cast this
  have hB : lowOdd (n + 1) (champLen C n) ≤
      ((Finset.range (champLen C n)).filter
        fun i => i + (altWord 4).length ≤ champLen C n ∧
          WindowMatch (fun s => (altWord 4).getD s false) (altWord 4).length i
            (n + 1)).card + 83 := by omega
  have hBR : (lowOdd (n + 1) (champLen C n) : ℝ) ≤
      (((Finset.range (champLen C n)).filter
        fun i => i + (altWord 4).length ≤ champLen C n ∧
          WindowMatch (fun s => (altWord 4).getD s false) (altWord 4).length i
            (n + 1)).card : ℕ) + 83 := by exact_mod_cast hB
  linarith

/-- **Drift, summed.**  For every `C ≥ 5` and `N`, with no hypothesis: a shortage of odd letters
below `1/2`, or else interior blocks `(10)^4`.  Here `P`, `O`, `A` are as in the module docstring. -/
theorem drift_total (C : ℕ) (hC : 5 ≤ C) (N : ℕ) :
    (cum (champLen C) N : ℝ) -
        (interior C (fun s => [true].getD s false) [true].length N : ℝ) ≤
      (cum (champLen C) N : ℝ) / 5 +
        0.59 * (interior C (fun s => [true].getD s false) [true].length N : ℝ) +
        0.41 * ((interior C (fun s => (altWord 4).getD s false) (altWord 4).length N : ℝ) +
          83 * N) := by
  have hC1 : 1 ≤ C := by omega
  have hCR : (5 : ℝ) ≤ C := by exact_mod_cast hC
  set S : ℝ := ∑ n ∈ Finset.range N, (Nat.size (n + 1) : ℝ) with hS
  set OO : ℝ := ∑ n ∈ Finset.range N,
    ((highOdd (n + 1) (champLen C n) : ℝ) + lowOdd (n + 1) (champLen C n)) with hOO
  set WW : ℝ := ∑ n ∈ Finset.range N, ((((Finset.range (champLen C n)).filter
    fun i => i + (altWord 4).length ≤ champLen C n ∧
      WindowMatch (fun s => (altWord 4).getD s false) (altWord 4).length i (n + 1)).card : ℕ) : ℝ)
    with hWW
  have hP : (cum (champLen C) N : ℝ) = C * S := by
    rw [cum_eq_mul_sum_size C hC1, hS]
    push_cast
    rfl
  have hO : (interior C (fun s => [true].getD s false) [true].length N : ℝ) = OO := by
    rw [interior_true_eq, hOO]
    push_cast
    rfl
  have hA : (interior C (fun s => (altWord 4).getD s false) (altWord 4).length N : ℝ) = WW := by
    rw [hWW]
    simp only [interior]
    push_cast
    rfl
  have hsum : ∑ n ∈ Finset.range N,
        ((C : ℝ) * (Nat.size (n + 1) : ℝ) -
          ((highOdd (n + 1) (champLen C n) : ℝ) + lowOdd (n + 1) (champLen C n))) ≤
      ∑ n ∈ Finset.range N,
        ((Nat.size (n + 1) : ℝ) +
          0.59 * ((highOdd (n + 1) (champLen C n) : ℝ) + lowOdd (n + 1) (champLen C n)) +
          0.41 * (((((Finset.range (champLen C n)).filter
            fun i => i + (altWord 4).length ≤ champLen C n ∧
              WindowMatch (fun s => (altWord 4).getD s false) (altWord 4).length i
                (n + 1)).card : ℕ) : ℝ) + 83)) :=
    Finset.sum_le_sum fun n _ => word_drift C hC1 n
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  rw [Finset.sum_add_distrib] at hOO
  rw [← hS, ← hOO, ← hWW] at hsum
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have h5 : 5 * S ≤ C * S := mul_le_mul_of_nonneg_right hCR hS0
  rw [hP, hO, hA]
  linarith

/-- **`𝒞_C` is not normal for `C ≥ 5`.** -/
theorem not_normal_of_five_le (C : ℕ) (hC : 5 ≤ C) : ¬ Normal (collatzChampernowne C) := by
  intro hN
  set P : ℕ → ℕ := cum (champLen C) with hPdef
  have hPtop : Tendsto P atTop atTop :=
    tendsto_atTop_mono (le_cum (champLen C) (one_le_champLen C)) tendsto_id
  have h1 := (hN [true]).comp hPtop
  have h2 := (hN (altWord 4)).comp hPtop
  have h3 := tendsto_succ_div_cum C
  have hT := ((h1.const_mul (1.59 : ℝ)).add (h2.const_mul (0.41 : ℝ))).add
    (h3.const_mul (34.03 : ℝ))
  have hlim : (1.59 : ℝ) * (1 / 2) ^ [true].length + 0.41 * (1 / 2) ^ (altWord 4).length +
      34.03 * 0 < 0.8 := by
    rw [length_altWord]
    norm_num
  obtain ⟨N, hlt, hN1⟩ := ((hT.eventually_lt_const hlim).and
    (eventually_ge_atTop 1)).exists
  simp only [Function.comp] at hlt
  have hPN : (N : ℝ) ≤ P N := by exact_mod_cast le_cum (champLen C) (one_le_champLen C) N
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hP0 : (0 : ℝ) < P N := by linarith
  have hd := drift_total C hC N
  have ho := occ_cum_le C [true] N
  have ha := occ_cum_le C (altWord 4) N
  have hoR : (interior C (fun s => [true].getD s false) [true].length N : ℝ) ≤
      occ (collatzChampernowne C) [true] (P N) := by exact_mod_cast ho.1
  have haR : (interior C (fun s => (altWord 4).getD s false) (altWord 4).length N : ℝ) ≤
      occ (collatzChampernowne C) (altWord 4) (P N) := by exact_mod_cast ha.1
  have hmul : (1.59 : ℝ) * (occ (collatzChampernowne C) [true] (P N) : ℝ) +
      0.41 * (occ (collatzChampernowne C) (altWord 4) (P N) : ℝ) + 34.03 * ((N : ℝ) + 1) <
      0.8 * P N := by
    have := mul_lt_mul_of_pos_right hlt hP0
    have heq : ((1.59 : ℝ) * ((occ (collatzChampernowne C) [true] (P N) : ℝ) / (P N : ℝ)) +
        0.41 * ((occ (collatzChampernowne C) (altWord 4) (P N) : ℝ) / (P N : ℝ)) +
        34.03 * (((N : ℝ) + 1) / (P N : ℝ))) * (P N : ℝ) =
        (1.59 : ℝ) * (occ (collatzChampernowne C) [true] (P N) : ℝ) +
        0.41 * (occ (collatzChampernowne C) (altWord 4) (P N) : ℝ) + 34.03 * ((N : ℝ) + 1) := by
      field_simp
    rw [← heq]
    exact this
  change (P N : ℝ) - _ ≤ (P N : ℝ) / 5 + _ + _ at hd
  linarith

/-- **The threshold conjecture, above `C*`, is a theorem.** -/
theorem champernowneNotNormalAboveThreshold : ChampernowneNotNormalAboveThreshold :=
  not_normal_of_five_le

end CollatzMoonshot.Conjugacy
