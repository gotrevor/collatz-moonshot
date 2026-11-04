/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.ChampernowneDrift

/-!
# `𝒞_C` in logarithmic density

Natural-density normality of `𝒞_C` for `1 < C < C*` asks about every stage.  Logarithmic density
averages over stages, because a position in the word of `n` carries log-weight about `1 / (C s n)`,
and the word has `C s` letters, so the word carries log-weight `1 / n`.  So `LogNormal (𝒞_C)` follows
from a statement about single orbits, in the logarithmic density of the starts (`OrbitWordLaw`,
`logNormal_of_orbitWordLaw`).

The orbit statement should follow from Tao 2019, through a chain of his Proposition 1.11 over scales
(`orbitWordLaw_of_le_four` in `OrbitWordLaw.lean`, believed; research note §16).

Above the threshold nothing of this kind can hold (`not_logNormal_of_five_le`), by `drift_total` under
partial summation.  So in logarithmic density the threshold would be sharp.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- The logarithmic frequency of `u` in `w` among positions below `P`. -/
noncomputable def logFreq (w : ℕ → Bool) (u : List Bool) (P : ℕ) : ℝ :=
  (∑ i ∈ (Finset.range P).filter (fun i => OccursAt w u i), (1 : ℝ) / (i + 1)) / Real.log P

/-- Normal in logarithmic density: every block `u` has logarithmic frequency `2^(−|u|)`. -/
def LogNormal (w : ℕ → Bool) : Prop :=
  ∀ u : List Bool, Tendsto (logFreq w u) atTop (𝓝 ((1 / 2 : ℝ) ^ u.length))

/-- The indicator of an occurrence of `u` at position `i`. -/
noncomputable def occInd (w : ℕ → Bool) (u : List Bool) (i : ℕ) : ℝ :=
  if OccursAt w u i then 1 else 0

/-- The logarithmically weighted count of occurrences below `P`. -/
noncomputable def logSum (w : ℕ → Bool) (u : List Bool) (P : ℕ) : ℝ :=
  ∑ i ∈ Finset.range P, occInd w u i / ((i : ℝ) + 1)

/-- The weighted count is the numerator of `logFreq`. -/
theorem logFreq_eq (w : ℕ → Bool) (u : List Bool) (P : ℕ) :
    logFreq w u P = logSum w u P / Real.log P := by
  simp only [logFreq, logSum, occInd, Finset.sum_filter, ite_div, zero_div]

/-- The indicator sums to `occ`. -/
theorem sum_occInd (w : ℕ → Bool) (u : List Bool) (P : ℕ) :
    ∑ i ∈ Finset.range P, occInd w u i = (occ w u P : ℝ) := by
  simp only [occ, occInd, Finset.card_filter]
  push_cast
  rfl

/-- The indicator lies in `[0, 1]`. -/
theorem occInd_nonneg (w : ℕ → Bool) (u : List Bool) (i : ℕ) : 0 ≤ occInd w u i := by
  unfold occInd; split_ifs <;> norm_num

/-- The indicator lies in `[0, 1]`. -/
theorem occInd_le_one (w : ℕ → Bool) (u : List Bool) (i : ℕ) : occInd w u i ≤ 1 := by
  unfold occInd; split_ifs <;> norm_num

/-- **Partial summation** against the weights `1 / (i + 1)`. -/
theorem partial_sum (x : ℕ → ℝ) (P : ℕ) :
    ∑ i ∈ Finset.range P, x i / ((i : ℝ) + 1) =
      (∑ i ∈ Finset.range P, x i) / ((P : ℝ) + 1) +
        ∑ j ∈ Finset.range P, ((∑ i ∈ Finset.range (j + 1), x i) / ((j : ℝ) + 2)) / ((j : ℝ) + 1) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun j =>
      ((∑ i ∈ Finset.range (j + 1), x i) / ((j : ℝ) + 2)) / ((j : ℝ) + 1)),
      Finset.sum_range_succ x P]
    push_cast
    have h1 : ((P : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((P : ℝ) + 2) ≠ 0 := by positivity
    have h3 : ((P : ℝ) + 1 + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- The harmonic sum stays within `1` above `log`. -/
theorem harm_bounds (P : ℕ) :
    Real.log P ≤ ∑ i ∈ Finset.range P, 1 / ((i : ℝ) + 1) ∧
      ∑ i ∈ Finset.range P, 1 / ((i : ℝ) + 1) ≤ 1 + Real.log P := by
  have he : ∑ i ∈ Finset.range P, 1 / ((i : ℝ) + 1) = ((harmonic P : ℚ) : ℝ) := by
    simp [harmonic]
  rw [he]
  refine ⟨?_, harmonic_le_one_add_log P⟩
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · simp
  · refine le_trans (Real.log_le_log (by exact_mod_cast hP) ?_) (log_add_one_le_harmonic P)
    push_cast; linarith

/-- `log` of a position tends to infinity. -/
theorem tendsto_log_nat : Tendsto (fun P : ℕ => Real.log P) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- A bounded numerator over `log` tends to `0`. -/
theorem tendsto_bdd_div_log (f : ℕ → ℝ) (K : ℝ) (hf : ∀ P, |f P| ≤ K) :
    Tendsto (fun P : ℕ => f P / Real.log P) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := K)).div_atTop tendsto_log_nat
  refine squeeze_zero_norm' ?_ h
  filter_upwards [tendsto_log_nat.eventually_gt_atTop 0] with P hP
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hP]
  exact div_le_div_of_nonneg_right (hf P) hP.le

/-- The harmonic sum over `log` tends to `1`. -/
theorem tendsto_harm_div_log :
    Tendsto (fun P : ℕ => (∑ i ∈ Finset.range P, 1 / ((i : ℝ) + 1)) / Real.log P) atTop (𝓝 1) := by
  have h : Tendsto (fun P : ℕ => 1 + 1 / Real.log P) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_bdd_div_log (fun _ => 1) 1 (by simp))
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [tendsto_log_nat.eventually_gt_atTop 0] with P hP
    rw [le_div_iff₀ hP, one_mul]
    exact (harm_bounds P).1
  · filter_upwards [tendsto_log_nat.eventually_gt_atTop 0] with P hP
    rw [div_le_iff₀ hP]
    have := (harm_bounds P).2
    have e : (1 + 1 / Real.log P) * Real.log P = Real.log P + 1 := by field_simp
    linarith

/-- **The Stolz step.**  If `v` is eventually at most `η` plus a term `t` of logarithmic mean zero,
for each `η > 0`, then `v` has logarithmic mean zero. -/
theorem tendsto_log_mean_zero (v : ℕ → ℝ)
    (hv : ∀ η > 0, ∃ t : ℕ → ℝ, (∀ n, 0 ≤ t n) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, t n / ((n : ℝ) + 1)) / Real.log N) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, |v n| ≤ η + t n) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, v n / ((n : ℝ) + 1)) / Real.log N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨t, ht0, htl, hte⟩ := hv (ε / 8) (by positivity)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hte
  set K := ∑ n ∈ Finset.range N0, |v n| / ((n : ℝ) + 1) with hK
  have hsum : ∀ N, N0 ≤ N → ∑ n ∈ Finset.range N, |v n| / ((n : ℝ) + 1) ≤
      K + ∑ n ∈ Finset.range N, (ε / 8 + t n) / ((n : ℝ) + 1) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      have : 0 ≤ ∑ n ∈ Finset.range N0, (ε / 8 + t n) / ((n : ℝ) + 1) :=
        Finset.sum_nonneg fun n _ => div_nonneg (add_nonneg (by positivity) (ht0 n)) (by positivity)
      linarith
    | succ N hN ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun n => (ε / 8 + t n) / ((n : ℝ) + 1))]
      have := div_le_div_of_nonneg_right (hN0 N hN) (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
      linarith
  have h1 := (tendsto_const_nhds (x := K)).div_atTop tendsto_log_nat
  have e1 := (Metric.tendsto_atTop.mp h1) (ε / 4) (by positivity)
  have e2 := (Metric.tendsto_atTop.mp htl) (ε / 4) (by positivity)
  obtain ⟨A1, hA1⟩ := e1
  obtain ⟨A2, hA2⟩ := e2
  obtain ⟨A3, hA3⟩ := eventually_atTop.mp
    (tendsto_harm_div_log.eventually_lt_const (show (1 : ℝ) < 2 by norm_num))
  obtain ⟨A4, hA4⟩ := eventually_atTop.mp (tendsto_log_nat.eventually_gt_atTop 0)
  refine ⟨max N0 (max A1 (max A2 (max A3 A4))), fun N hN => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨hN0', hN1, hN2, hN3, hN4⟩ := hN
  have hl := hA4 N hN4
  have b1 := hA1 N hN1
  have b2 := hA2 N hN2
  have b3 := hA3 N hN3
  rw [Real.dist_eq, sub_zero] at b1 b2 ⊢
  rw [abs_lt] at b1 b2
  have hs := hsum N hN0'
  have habs : |∑ n ∈ Finset.range N, v n / ((n : ℝ) + 1)| ≤
      ∑ n ∈ Finset.range N, |v n| / ((n : ℝ) + 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  have hsplit : ∑ n ∈ Finset.range N, (ε / 8 + t n) / ((n : ℝ) + 1) =
      ε / 8 * ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) +
        ∑ n ∈ Finset.range N, t n / ((n : ℝ) + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [abs_div, abs_of_pos hl, div_lt_iff₀ hl]
  rw [div_lt_iff₀ hl] at b3
  have b1' : K < ε / 4 * Real.log N := by
    have := b1.2; rwa [div_lt_iff₀ hl] at this
  have b2' : ∑ n ∈ Finset.range N, t n / ((n : ℝ) + 1) < ε / 4 * Real.log N := by
    have := b2.2; rwa [div_lt_iff₀ hl] at this
  have b3' : ε / 8 * ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ≤ ε / 8 * (2 * Real.log N) :=
    mul_le_mul_of_nonneg_left b3.le (by positivity)
  nlinarith

/-- A sequence tending to `0` has logarithmic mean zero. -/
theorem tendsto_log_mean_zero_of_tendsto (v : ℕ → ℝ) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, v n / ((n : ℝ) + 1)) / Real.log N)
      atTop (𝓝 0) := by
  refine tendsto_log_mean_zero v fun η hη => ⟨fun _ => 0, fun _ => le_rfl, by simp, ?_⟩
  have h := (Metric.tendsto_atTop.mp hv) η hη
  obtain ⟨N, hN⟩ := h
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [Real.dist_eq, sub_zero] at this
  linarith

/-- A sequence tending to `a` has logarithmic mean `a`. -/
theorem tendsto_log_mean (g : ℕ → ℝ) (a : ℝ) (hg : Tendsto g atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g n / ((n : ℝ) + 1)) / Real.log N)
      atTop (𝓝 a) := by
  have h0 := tendsto_log_mean_zero_of_tendsto (fun n => g n - a)
    (by simpa using hg.sub_const a)
  have h1 := h0.add (tendsto_harm_div_log.const_mul a)
  rw [zero_add, mul_one] at h1
  refine h1.congr fun N => ?_
  rw [mul_div_assoc', ← add_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by ring

/-- Shifting a density by one position in numerator and denominator keeps its limit. -/
theorem tendsto_occ_shift (f : ℕ → ℝ) (a : ℝ) (hf : Tendsto (fun k : ℕ => f k / k) atTop (𝓝 a)) :
    Tendsto (fun j : ℕ => f (j + 1) / ((j : ℝ) + 2)) atTop (𝓝 a) := by
  have h1 := hf.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun j : ℕ => ((j : ℝ) + 1) / ((j : ℝ) + 2)) atTop (𝓝 1) := by
    have h3 : Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 2)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub ((tendsto_const_nhds).div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
    rw [sub_zero] at h3
    refine h3.congr fun j => ?_
    have : ((j : ℝ) + 2) ≠ 0 := by positivity
    field_simp; ring
  have h4 := h1.mul h2
  rw [mul_one] at h4
  refine h4.congr fun j => ?_
  simp only [Function.comp]
  push_cast
  have h5 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have h6 : ((j : ℝ) + 2) ≠ 0 := by positivity
  field_simp

/-- Normality implies logarithmic normality, by partial summation. -/
theorem logNormal_of_normal (w : ℕ → Bool) (h : Normal w) : LogNormal w := by
  intro u
  have hs := tendsto_occ_shift (fun k => (occ w u k : ℝ)) _ (h u)
  have hm := tendsto_log_mean _ _ hs
  have hb := tendsto_bdd_div_log (fun P => (occ w u P : ℝ) / ((P : ℝ) + 1)) 1 fun P => by
    have h1 : (occ w u P : ℝ) ≤ P := by
      have : occ w u P ≤ P := by
        simpa [occ] using Finset.card_filter_le (Finset.range P) (fun i => OccursAt w u i)
      exact_mod_cast this
    rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
    linarith
  have hT := hb.add hm
  rw [zero_add] at hT
  refine hT.congr fun P => ?_
  rw [logFreq_eq, logSum, partial_sum (occInd w u) P, sum_occInd, add_div]
  simp only [sum_occInd]

/-- A start is **bad** for `u` at level `δ` if its word of `C s` letters holds a number of interior
occurrences of `u` off by more than `δ s` from `C s 2^(−|u|)`. -/
def BadStart (C : ℕ) (u : List Bool) (δ : ℝ) (n : ℕ) : Prop :=
  δ * Nat.size n < |((((Finset.range (C * Nat.size n)).filter fun i =>
      i + u.length ≤ C * Nat.size n ∧
        WindowMatch (fun s => u.getD s false) u.length i n).card : ℕ) : ℝ) -
    (C * Nat.size n : ℕ) * (1 / 2 : ℝ) ^ u.length|

open Classical in
/-- **Node: the orbit word law.**  For every word `u` and `δ > 0`, the bad starts have logarithmic
density `0`.  So for almost every start in logarithmic density, the first `C log₂ n` parity letters
have the right frequency of every word. -/
def OrbitWordLaw (C : ℕ) : Prop :=
  ∀ (u : List Bool) (δ : ℝ), 0 < δ → Tendsto
    (fun X : ℕ => (∑ n ∈ (Finset.Ico 1 X).filter (BadStart C u δ), (1 : ℝ) / n) / Real.log X)
    atTop (𝓝 0)

/-- `occ` is monotone in the position. -/
theorem occ_mono (w : ℕ → Bool) (u : List Bool) {a b : ℕ} (h : a ≤ b) : occ w u a ≤ occ w u b :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

/-- The word index tends to infinity with the position. -/
theorem tendsto_wordIndex (C : ℕ) :
    Tendsto (wordIndex (champLen C) (one_le_champLen C)) atTop atTop := by
  refine tendsto_atTop.2 fun M => eventually_atTop.2 ⟨cum (champLen C) M, fun K hK => ?_⟩
  by_contra hlt
  have h1 := (cum_le_wordIndex C K).2
  have h2 := cum_mono (champLen C)
    (show wordIndex (champLen C) (one_le_champLen C) K + 1 ≤ M by omega)
  omega

/-- The word index is at most the position. -/
theorem wordIndex_le (C K : ℕ) : wordIndex (champLen C) (one_le_champLen C) K ≤ K :=
  (le_cum (champLen C) (one_le_champLen C) _).trans (cum_le_wordIndex C K).1

/-- The word index is `o(position)`. -/
theorem tendsto_wordIndex_div (C : ℕ) : Tendsto
    (fun K : ℕ => ((wordIndex (champLen C) (one_le_champLen C) K : ℝ) + 1) / K) atTop (𝓝 0) := by
  have h := (tendsto_succ_div_cum C).comp (tendsto_wordIndex C)
  refine squeeze_zero' (Eventually.of_forall fun K => by positivity) ?_ h
  filter_upwards [(tendsto_wordIndex C).eventually_ge_atTop 1] with K hK
  simp only [Function.comp]
  have h1 := (cum_le_wordIndex C K).1
  have h2 := le_cum (champLen C) (one_le_champLen C)
    (wordIndex (champLen C) (one_le_champLen C) K)
  have h3 : (0 : ℝ) < cum (champLen C) (wordIndex (champLen C) (one_le_champLen C) K) := by
    exact_mod_cast (by omega :
      0 < cum (champLen C) (wordIndex (champLen C) (one_le_champLen C) K))
  exact div_le_div_of_nonneg_left (by positivity) h3 (by exact_mod_cast h1)

/-- Deficit of the bit-length sum: `n size(n+1) ≤ ∑_{m<n} size(m+1) + 2^size(n+1)`. -/
theorem mul_size_le_sum (n : ℕ) :
    n * Nat.size (n + 1) ≤ (∑ m ∈ Finset.range n, Nat.size (m + 1)) + 2 ^ Nat.size (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    set s := Nat.size (n + 1) with hs
    have h1 : n + 1 < 2 ^ s := Nat.lt_size_self (n + 1)
    have h2 : s ≤ Nat.size (n + 1 + 1) := Nat.size_le_size (by omega)
    have h3 : Nat.size (n + 1 + 1) ≤ s + 1 := Nat.size_le.mpr (by rw [pow_succ]; omega)
    rcases (by omega : Nat.size (n + 1 + 1) = s ∨ Nat.size (n + 1 + 1) = s + 1) with e | e
    · rw [e]; nlinarith
    · rw [e, pow_succ]; nlinarith

/-- For `C ≥ 1`, the word starts are `C` times the sum of bit lengths. -/
theorem cum_eq_mul_sum (C : ℕ) (hC : 1 ≤ C) (n : ℕ) :
    cum (champLen C) n = C * ∑ m ∈ Finset.range n, Nat.size (m + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [cum_succ, ih, Finset.sum_range_succ, champLen, max_eq_left hC, mul_add]

/-- Word lengths increase, so a start is at most index times length. -/
theorem cum_le_mul_len (C n : ℕ) : cum (champLen C) n ≤ n * champLen C n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : champLen C n ≤ champLen C (n + 1) :=
      Nat.mul_le_mul_left _ (Nat.size_le_size (by omega))
    rw [cum_succ]
    calc cum (champLen C) n + champLen C n ≤ n * champLen C n + champLen C n := by omega
      _ = (n + 1) * champLen C n := by ring
      _ ≤ (n + 1) * champLen C (n + 1) := Nat.mul_le_mul_left _ hm

/-- A word start is close to index times length: the sharp direction. -/
theorem mul_len_le_cum (C : ℕ) (hC : 1 ≤ C) (n : ℕ) :
    (n + 1) * champLen C n ≤ cum (champLen C) n + 3 * C * (n + 1) := by
  have h := mul_size_le_sum n
  have hs : Nat.size (n + 1) ≤ n + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have hp : 2 ^ Nat.size (n + 1) ≤ 2 * (n + 1) := by
    have hpos : 0 < Nat.size (n + 1) := Nat.size_pos.mpr n.succ_pos
    obtain ⟨k, hk⟩ : ∃ k, Nat.size (n + 1) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have : 2 ^ k ≤ n + 1 := Nat.lt_size.mp (by omega)
    rw [hk, pow_succ]; omega
  rw [cum_eq_mul_sum C hC, champLen, max_eq_left hC]
  have h4 := Nat.mul_le_mul_left C h
  have h5 := Nat.mul_le_mul_left C hs
  have h6 := Nat.mul_le_mul_left C hp
  nlinarith

/-- The occurrences of `u` starting in the word of index `n`. -/
noncomputable def wordHits (C : ℕ) (u : List Bool) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (champLen C n), occInd (collatzChampernowne C) u (cum (champLen C) n + i)

/-- The log weight of the occurrences starting in the word of index `n`. -/
noncomputable def wordWeight (C : ℕ) (u : List Bool) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (champLen C n), occInd (collatzChampernowne C) u (cum (champLen C) n + i) /
    (((cum (champLen C) n + i : ℕ) : ℝ) + 1)

/-- The weighted count at a word start is the sum of word weights. -/
theorem logSum_cum (C : ℕ) (u : List Bool) (N : ℕ) :
    logSum (collatzChampernowne C) u (cum (champLen C) N) =
      ∑ n ∈ Finset.range N, wordWeight C u n := by
  induction N with
  | zero => simp [logSum]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih, cum_succ]
    simp only [logSum, wordWeight, Finset.sum_range_add]

/-- The weighted count is monotone. -/
theorem logSum_mono (w : ℕ → Bool) (u : List Bool) {a b : ℕ} (h : a ≤ b) :
    logSum w u a ≤ logSum w u b :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun i _ _ =>
    div_nonneg (occInd_nonneg w u i) (by positivity)

/-- The weighted count is nonnegative. -/
theorem logSum_nonneg (w : ℕ → Bool) (u : List Bool) (P : ℕ) : 0 ≤ logSum w u P :=
  Finset.sum_nonneg fun i _ => div_nonneg (occInd_nonneg w u i) (by positivity)

/-- The straddling windows are at most the word length of `u`. -/
theorem wordHits_bounds (C : ℕ) (u : List Bool) (n : ℕ) :
    (((Finset.range (champLen C n)).filter fun i => i + u.length ≤ champLen C n ∧
        WindowMatch (fun s => u.getD s false) u.length i (n + 1)).card : ℝ) ≤ wordHits C u n ∧
    wordHits C u n ≤ (((Finset.range (champLen C n)).filter fun i => i + u.length ≤ champLen C n ∧
        WindowMatch (fun s => u.getD s false) u.length i (n + 1)).card : ℝ) + u.length := by
  have he : wordHits C u n = (((Finset.range (champLen C n)).filter fun i =>
      OccursAt (collatzChampernowne C) u (cum (champLen C) n + i)).card : ℝ) := by
    simp only [wordHits, occInd, Finset.card_filter]
    push_cast
    rfl
  rw [he]
  set z := champLen C n with hz
  constructor
  · refine Nat.cast_le.mpr (Finset.card_le_card fun i hi => ?_)
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, (occursAt_cum_iff C u n i hi.2.1).mpr hi.2.2⟩
  · have hsub : ((Finset.range z).filter fun i =>
        OccursAt (collatzChampernowne C) u (cum (champLen C) n + i)) ⊆
        ((Finset.range z).filter fun i => i + u.length ≤ z ∧
          WindowMatch (fun s => u.getD s false) u.length i (n + 1)) ∪
        Finset.Ico (z - u.length) z := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hi ⊢
      by_cases h : i + u.length ≤ z
      · exact Or.inl ⟨hi.1, h, (occursAt_cum_iff C u n i h).mp hi.2⟩
      · exact Or.inr ⟨by omega, hi.1⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Nat.card_Ico] at hc
    have hc' : ((Finset.range z).filter fun i =>
        OccursAt (collatzChampernowne C) u (cum (champLen C) n + i)).card ≤
        ((Finset.range z).filter fun i => i + u.length ≤ z ∧
          WindowMatch (fun s => u.getD s false) u.length i (n + 1)).card + u.length := by omega
    exact_mod_cast hc'

/-- The hit count is between `0` and the word length. -/
theorem wordHits_nonneg_le (C : ℕ) (u : List Bool) (n : ℕ) :
    0 ≤ wordHits C u n ∧ wordHits C u n ≤ champLen C n := by
  constructor
  · exact Finset.sum_nonneg fun i _ => occInd_nonneg _ _ _
  · have := Finset.sum_le_card_nsmul (Finset.range (champLen C n))
      (fun i => occInd (collatzChampernowne C) u (cum (champLen C) n + i)) 1
      fun i _ => occInd_le_one _ _ _
    simpa [wordHits] using this

/-- The relative error in the weight of a word. -/
noncomputable def wordErr (C n : ℕ) : ℝ :=
  3 * C * (((n : ℝ) + 1) / ((cum (champLen C) n : ℝ) + 1))

/-- The weight of a word, scaled by its integer, is its hit frequency up to `wordErr`. -/
theorem wordWeight_bounds (C : ℕ) (hC : 1 ≤ C) (u : List Bool) (n : ℕ) :
    wordHits C u n / champLen C n ≤ ((n : ℝ) + 1) * wordWeight C u n ∧
      ((n : ℝ) + 1) * wordWeight C u n ≤ wordHits C u n / champLen C n + wordErr C n := by
  set c : ℝ := ((cum (champLen C) n : ℕ) : ℝ) with hc
  set l : ℝ := ((champLen C n : ℕ) : ℝ) with hl
  set b := wordHits C u n with hb
  have hc0 : 0 ≤ c := by positivity
  have hl0 : 0 < l := by
    have := one_le_champLen C n
    rw [hl]; exact_mod_cast this
  have hb0 := (wordHits_nonneg_le C u n).1
  have hbl := (wordHits_nonneg_le C u n).2
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hup : ((n : ℝ) + 1) * l ≤ c + 3 * C * ((n : ℝ) + 1) := by
    have := mul_len_le_cum C hC n
    rw [hc, hl]; exact_mod_cast this
  have hlow : c + l ≤ ((n : ℝ) + 1) * l := by
    have := cum_le_mul_len C n
    have h2 : (c : ℝ) ≤ n * l := by rw [hc, hl]; exact_mod_cast this
    nlinarith
  have hW1 : b / (c + l) ≤ wordWeight C u n := by
    rw [hb, wordHits, Finset.sum_div]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : (i : ℝ) + 1 ≤ l := by
      have := Finset.mem_range.mp hi
      rw [hl]; exact_mod_cast this
    refine div_le_div_of_nonneg_left (occInd_nonneg _ _ _) (by positivity) ?_
    push_cast; rw [← hc]; linarith
  have hW2 : wordWeight C u n ≤ b / (c + 1) := by
    rw [hb, wordHits, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    refine div_le_div_of_nonneg_left (occInd_nonneg _ _ _) (by positivity) ?_
    push_cast; rw [← hc]
    have : (0 : ℝ) ≤ i := by positivity
    linarith
  constructor
  · have h1 : b / l ≤ ((n : ℝ) + 1) * (b / (c + l)) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hl0 (by positivity)]
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_left hW1 hn0.le)
  · have hq0 : 0 ≤ b / l := div_nonneg hb0 hl0.le
    have hq1 : b / l ≤ 1 := (div_le_one hl0).mpr hbl
    have hτ : 0 ≤ wordErr C n := by unfold wordErr; positivity
    have hkey : ((n : ℝ) + 1) * (b / (c + 1)) = b / l * (((n : ℝ) + 1) * l / (c + 1)) := by
      field_simp
    have hR : ((n : ℝ) + 1) * l / (c + 1) ≤ 1 + wordErr C n := by
      have eτ : wordErr C n * (c + 1) = 3 * C * ((n : ℝ) + 1) := by
        have : c + 1 ≠ 0 := by positivity
        unfold wordErr
        rw [← hc]
        field_simp
      have e : (1 + wordErr C n) * (c + 1) = c + 1 + 3 * C * ((n : ℝ) + 1) := by
        rw [add_mul, one_mul, eτ]
      rw [div_le_iff₀ (by positivity), e]
      linarith
    have h1 := mul_le_mul_of_nonneg_left hW2 hn0.le
    rw [hkey] at h1
    have h2 := mul_le_mul_of_nonneg_left hR hq0
    nlinarith

/-- The relative error tends to `0`. -/
theorem tendsto_wordErr (C : ℕ) : Tendsto (wordErr C) atTop (𝓝 0) := by
  have h := (tendsto_succ_div_cum C).const_mul (3 * (C : ℝ))
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun n => by unfold wordErr; positivity) ?_ h
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold wordErr
  have h2 := le_cum (champLen C) (one_le_champLen C) n
  have h3 : (0 : ℝ) < cum (champLen C) n := by exact_mod_cast (by omega : 0 < cum (champLen C) n)
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left (by positivity) h3 (by linarith)) (by positivity)

/-- The bit length tends to infinity. -/
theorem tendsto_size_succ : Tendsto (fun n : ℕ => Nat.size (n + 1)) atTop atTop :=
  tendsto_atTop.2 fun M => eventually_atTop.2 ⟨2 ^ M, fun n hn =>
    (Nat.size_le_size (show 2 ^ M ≤ n + 1 by omega)).trans' (by rw [Nat.size_pow]; omega)⟩

/-- A good start has weight `a / n` up to `δ`, the straddling windows and `wordErr`. -/
theorem abs_weight_good (C : ℕ) (hC : 1 ≤ C) (u : List Bool) (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ)
    (hn : ¬ BadStart C u δ (n + 1)) :
    |((n : ℝ) + 1) * wordWeight C u n - (1 / 2 : ℝ) ^ u.length| ≤
      δ + (u.length : ℝ) / Nat.size (n + 1) + wordErr C n := by
  have hl : champLen C n = C * Nat.size (n + 1) := by rw [champLen, max_eq_left hC]
  rw [BadStart, not_lt, ← hl] at hn
  obtain ⟨h1, h2⟩ := wordHits_bounds C u n
  obtain ⟨h3, h4⟩ := wordWeight_bounds C hC u n
  have hτ : 0 ≤ wordErr C n := by unfold wordErr; positivity
  set a : ℝ := (1 / 2 : ℝ) ^ u.length with ha
  set s : ℝ := (Nat.size (n + 1) : ℝ) with hs
  have hs0 : 0 < s := by
    rw [hs]; exact_mod_cast Nat.size_pos.mpr n.succ_pos
  set l : ℝ := ((champLen C n : ℕ) : ℝ) with hlr
  have hls : s ≤ l := by
    rw [hlr, hs]; exact_mod_cast (Nat.le_mul_of_pos_left _ hC : _ ≤ C * Nat.size (n + 1)).trans_eq hl.symm
  have hl0 : 0 < l := by linarith
  rw [abs_le] at hn
  have hL0 : (0 : ℝ) ≤ u.length := by positivity
  have hq : |wordHits C u n / l - a| ≤ δ + (u.length : ℝ) / s := by
    have e : wordHits C u n / l - a = (wordHits C u n - l * a) / l := by field_simp
    have hb : |wordHits C u n - l * a| ≤ δ * s + u.length := by
      rw [abs_le]; constructor <;> linarith [hn.1, hn.2]
    rw [e, abs_div, abs_of_pos hl0, div_le_iff₀ hl0]
    have e2 : (δ + (u.length : ℝ) / s) * s = δ * s + u.length := by field_simp
    have hm : (δ + (u.length : ℝ) / s) * s ≤ (δ + (u.length : ℝ) / s) * l :=
      mul_le_mul_of_nonneg_left hls (by positivity)
    linarith
  rw [abs_le] at hq ⊢
  constructor <;> linarith [hq.1, hq.2]

/-- Any start has scaled weight within `2` plus `wordErr` of `a`. -/
theorem abs_weight_any (C : ℕ) (hC : 1 ≤ C) (u : List Bool) (n : ℕ) :
    |((n : ℝ) + 1) * wordWeight C u n - (1 / 2 : ℝ) ^ u.length| ≤ 2 + wordErr C n := by
  obtain ⟨h3, h4⟩ := wordWeight_bounds C hC u n
  have hτ : 0 ≤ wordErr C n := by unfold wordErr; positivity
  obtain ⟨hb0, hbl⟩ := wordHits_nonneg_le C u n
  have hl0 : (0 : ℝ) < champLen C n := by exact_mod_cast one_le_champLen C n
  have hq0 := div_nonneg hb0 hl0.le
  have hq1 := (div_le_one hl0).mpr hbl
  have ha0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ u.length := by positivity
  have ha1 : (1 / 2 : ℝ) ^ u.length ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [abs_le]; constructor <;> linarith

/-- `log (size (N + 1))` is `o (log N)`. -/
theorem tendsto_log_size_div :
    Tendsto (fun N : ℕ => Real.log (Nat.size (N + 1)) / Real.log N) atTop (𝓝 0) := by
  have hy : Tendsto (fun N : ℕ => 2 + 2 * Real.log N) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_log_nat.const_mul_atTop (by norm_num))
  have hφ := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hy
  have h4 := hφ.const_mul (4 : ℝ)
  rw [mul_zero] at h4
  refine squeeze_zero' ?_ ?_ h4
  · filter_upwards [tendsto_log_nat.eventually_gt_atTop 0] with N hN
    exact div_nonneg (Real.log_natCast_nonneg _) hN.le
  · filter_upwards [tendsto_log_nat.eventually_ge_atTop 1, eventually_ge_atTop 1] with N hN hN1
    simp only [Function.comp, id]
    set x := Real.log N with hx
    set y := 2 + 2 * x with hy'
    have hy0 : 0 < y := by rw [hy']; linarith
    have hs1 : (1 : ℝ) ≤ Nat.size (N + 1) := by
      exact_mod_cast Nat.size_pos.mpr N.succ_pos
    have hsy : (Nat.size (N + 1) : ℝ) ≤ y := by
      have hpos := Nat.size_pos.mpr N.succ_pos
      obtain ⟨k, hk⟩ : ∃ k, Nat.size (N + 1) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      have hp : 2 ^ k ≤ N + 1 := Nat.lt_size.mp (by omega)
      have hp2 : ((2 : ℝ) ^ k) ≤ 2 * N := by
        have : (2 ^ k : ℕ) ≤ 2 * N := by omega
        exact_mod_cast this
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
      have hlog := Real.log_le_log (by positivity) hp2
      rw [Real.log_pow, Real.log_mul (by norm_num) hN0.ne'] at hlog
      have hl2 := Real.log_two_gt_d9
      rw [hk]; push_cast
      have hk0 : (0 : ℝ) ≤ k := by positivity
      rw [hy', hx]
      rw [← hx] at hlog ⊢
      have hl3 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      nlinarith
    have hlogy : Real.log (Nat.size (N + 1)) ≤ Real.log y := Real.log_le_log (by linarith) hsy
    have hly0 : 0 ≤ Real.log y := by
      exact Real.log_nonneg (by rw [hy']; linarith)
    have hx0 : 0 < x := by linarith
    rw [div_le_iff₀ hx0]
    have e : 4 * (Real.log y / y) * x = Real.log y * (4 * x / y) := by field_simp
    have h1 : 1 ≤ 4 * x / y := by
      rw [le_div_iff₀ hy0, hy']; linarith
    rw [e]
    nlinarith

/-- `log` of a word end is asymptotic to `log` of its index. -/
theorem tendsto_log_cum_div (C : ℕ) (hC : 1 ≤ C) :
    Tendsto (fun N : ℕ => Real.log (cum (champLen C) (N + 1)) / Real.log N) atTop (𝓝 1) := by
  have hCl := tendsto_bdd_div_log (fun _ => Real.log 2 + Real.log C)
    |Real.log 2 + Real.log C| (fun _ => le_rfl)
  have hU := (tendsto_const_nhds (x := (1 : ℝ))).add (hCl.add tendsto_log_size_div)
  simp only [add_zero] at hU
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
  · filter_upwards [tendsto_log_nat.eventually_gt_atTop 0, eventually_ge_atTop 1] with N hN hN1
    rw [le_div_iff₀ hN, one_mul]
    have h1 := le_cum (champLen C) (one_le_champLen C) (N + 1)
    exact Real.log_le_log (by exact_mod_cast hN1) (by exact_mod_cast (by omega : N ≤ cum (champLen C) (N + 1)))
  · filter_upwards [tendsto_log_nat.eventually_gt_atTop 0, eventually_ge_atTop 1] with N hN hN1
    have hb : cum (champLen C) (N + 1) ≤ 2 * N * C * Nat.size (N + 1) := by
      have h1 := cum_le_mul_len C N
      rw [cum_succ]
      have h2 : champLen C N = C * Nat.size (N + 1) := by rw [champLen, max_eq_left hC]
      rw [h2] at h1 ⊢
      have h3 : (N + 1) * (C * Nat.size (N + 1)) ≤ (2 * N) * (C * Nat.size (N + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      nlinarith
    have hpos : 0 < cum (champLen C) (N + 1) := by
      have := le_cum (champLen C) (one_le_champLen C) (N + 1); omega
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hC0 : (C : ℝ) ≠ 0 := by positivity
    have hs0 : ((Nat.size (N + 1) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.size_pos.mpr N.succ_pos).ne'
    have hbR : (cum (champLen C) (N + 1) : ℝ) ≤ 2 * N * C * Nat.size (N + 1) := by
      exact_mod_cast hb
    have hlog := Real.log_le_log (by exact_mod_cast hpos) hbR
    rw [Real.log_mul (by positivity) hs0, Real.log_mul (by positivity) hC0,
      Real.log_mul (by norm_num) hN0] at hlog
    rw [div_le_iff₀ hN]
    have e : (1 + ((Real.log 2 + Real.log C) / Real.log N +
        Real.log (Nat.size (N + 1)) / Real.log N)) * Real.log N =
        Real.log N + (Real.log 2 + Real.log C) + Real.log (Nat.size (N + 1)) := by
      field_simp
      ring
    rw [e]
    linarith

/-- `log (N + 1)` is asymptotic to `log N`. -/
theorem tendsto_log_succ_div :
    Tendsto (fun N : ℕ => Real.log ((N + 1 : ℕ) : ℝ) / Real.log N) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_log_cum_div 1 le_rfl) ?_ ?_
  · filter_upwards [tendsto_log_nat.eventually_gt_atTop 0, eventually_ge_atTop 1] with N hN hN1
    rw [le_div_iff₀ hN, one_mul]
    exact Real.log_le_log (by exact_mod_cast hN1) (by push_cast; linarith)
  · filter_upwards [tendsto_log_nat.eventually_gt_atTop 0] with N hN
    refine div_le_div_of_nonneg_right ?_ hN.le
    exact Real.log_le_log (by positivity)
      (by exact_mod_cast le_cum (champLen 1) (one_le_champLen 1) (N + 1))

open Classical in
/-- Bad starts have logarithmic mean zero, reindexed to word indices. -/
theorem tendsto_bad_mean (C : ℕ) (h : OrbitWordLaw C) (u : List Bool) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      (if BadStart C u δ (n + 1) then (3 : ℝ) else 0) / ((n : ℝ) + 1)) / Real.log N)
      atTop (𝓝 0) := by
  have h0 := (h u δ hδ).comp (tendsto_add_atTop_nat 1)
  have h1 := (h0.mul tendsto_log_succ_div).const_mul (3 : ℝ)
  simp only [mul_zero, zero_mul] at h1
  refine h1.congr' ?_
  filter_upwards [tendsto_log_nat.eventually_gt_atTop 0,
    (tendsto_log_nat.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop 0] with N hN hN'
  simp only [Function.comp] at hN' ⊢
  have e : ∑ n ∈ (Finset.Ico 1 (N + 1)).filter (BadStart C u δ), (1 : ℝ) / n =
      ∑ n ∈ Finset.range N, (if BadStart C u δ (n + 1) then (1 : ℝ) else 0) / ((n : ℝ) + 1) := by
    rw [Finset.sum_filter, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [add_comm 1 n]
    split_ifs <;> simp
  rw [e, div_mul_div_cancel₀ hN'.ne', mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> ring

/-- **The orbit word law gives logarithmic normality.**  The word of `n` carries log-weight `≈ 1 / n`,
straddling windows are `O(1 / log n)` of it, and letters are bounded, so bad starts of density `0`
contribute nothing. -/
theorem logNormal_of_orbitWordLaw (C : ℕ) (hC : 1 ≤ C) (h : OrbitWordLaw C) :
    LogNormal (collatzChampernowne C) := by
  classical
  intro u
  set a : ℝ := (1 / 2 : ℝ) ^ u.length with ha
  set c := cum (champLen C) with hc
  set w := collatzChampernowne C with hw
  -- word level
  have hv : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      (((n : ℝ) + 1) * wordWeight C u n - a) / ((n : ℝ) + 1)) / Real.log N) atTop (𝓝 0) := by
    refine tendsto_log_mean_zero _ fun η hη => ⟨fun n =>
      if BadStart C u (η / 3) (n + 1) then (3 : ℝ) else 0, fun n => by dsimp only; split_ifs <;> norm_num,
      tendsto_bad_mean C h u (η / 3) (by positivity), ?_⟩
    have hLs : Tendsto (fun n : ℕ => (u.length : ℝ) / Nat.size (n + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp tendsto_size_succ)
    filter_upwards [hLs.eventually_lt_const (show (0 : ℝ) < η / 3 by positivity),
      (tendsto_wordErr C).eventually_lt_const (show (0 : ℝ) < min 1 (η / 3) by positivity)]
      with n h1 h2
    have h2a := lt_of_lt_of_le h2 (min_le_left _ _)
    have h2b := lt_of_lt_of_le h2 (min_le_right _ _)
    by_cases hb : BadStart C u (η / 3) (n + 1)
    · rw [if_pos hb]
      have := abs_weight_any C hC u n
      linarith
    · rw [if_neg hb]
      have := abs_weight_good C hC u (η / 3) (by positivity) n hb
      linarith
  have hG : Tendsto (fun N : ℕ => logSum w u (c N) / Real.log N) atTop (𝓝 a) := by
    have h1 := hv.add (tendsto_harm_div_log.const_mul a)
    rw [zero_add, mul_one] at h1
    refine h1.congr fun N => ?_
    rw [hw, hc, logSum_cum, mul_div_assoc', ← add_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hratio := tendsto_log_cum_div C hC
  have hU : Tendsto (fun N : ℕ => logSum w u (c (N + 1)) / Real.log N) atTop (𝓝 a) := by
    have h1 := (hG.comp (tendsto_add_atTop_nat 1)).mul tendsto_log_succ_div
    rw [mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [(tendsto_log_nat.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop 0]
      with N hN
    simp only [Function.comp] at hN ⊢
    rw [div_mul_div_cancel₀ hN.ne']
  have hLo : Tendsto (fun N : ℕ => logSum w u (c N) / Real.log (c (N + 1))) atTop (𝓝 a) := by
    have h2 := hratio.inv₀ one_ne_zero
    have h1 := hG.mul h2
    rw [inv_one, mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [tendsto_log_nat.eventually_gt_atTop 0] with N hN
    rw [inv_div, div_mul_div_cancel₀ hN.ne']
  have hW := tendsto_wordIndex C
  have hLow := hLo.comp hW
  have hUp := hU.comp hW
  refine (tendsto_of_tendsto_of_tendsto_of_le_of_le' hLow hUp ?_ ?_).congr fun P => (logFreq_eq w u P).symm
  · filter_upwards [hW.eventually (tendsto_log_nat.eventually_gt_atTop 0)] with P hN
    simp only [Function.comp]
    set N := wordIndex (champLen C) (one_le_champLen C) P with hNdef
    obtain ⟨h1, h2⟩ := cum_le_wordIndex C P
    rw [← hNdef] at h1 h2
    have hNP : N ≤ P := (le_cum _ (one_le_champLen C) N).trans h1
    have hN1 : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · rw [h0] at hN; simp at hN
      · exact h0
    have hlogP : 0 < Real.log P := hN.trans_le (Real.log_le_log (by exact_mod_cast hN1)
      (by exact_mod_cast hNP))
    have hPc : Real.log P ≤ Real.log (c (N + 1)) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < P)) (by exact_mod_cast h2.le)
    exact (div_le_div_of_nonneg_left (logSum_nonneg _ _ _) hlogP hPc).trans
      (div_le_div_of_nonneg_right (logSum_mono _ _ h1) hlogP.le)
  · filter_upwards [hW.eventually (tendsto_log_nat.eventually_gt_atTop 0)] with P hN
    simp only [Function.comp]
    set N := wordIndex (champLen C) (one_le_champLen C) P with hNdef
    obtain ⟨h1, h2⟩ := cum_le_wordIndex C P
    rw [← hNdef] at h1 h2
    have hNP : N ≤ P := (le_cum _ (one_le_champLen C) N).trans h1
    have hN1 : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · rw [h0] at hN; simp at hN
      · exact h0
    have hlogN : Real.log N ≤ Real.log P :=
      Real.log_le_log (by exact_mod_cast hN1) (by exact_mod_cast hNP)
    exact (div_le_div_of_nonneg_right (logSum_mono _ _ h2.le) (hN.le.trans hlogN)).trans
      (div_le_div_of_nonneg_left (logSum_nonneg _ _ _) hN hlogN)

/-- `drift_total` at every position: the deficit is at most a multiple of the word index. -/
theorem drift_at (C : ℕ) (hC : 5 ≤ C) (j : ℕ) :
    0.8 * (j : ℝ) - 1.59 * (occ (collatzChampernowne C) [true] j : ℝ) -
        0.41 * (occ (collatzChampernowne C) (altWord 4) j : ℝ) ≤
      (34.03 + 0.8 * C) * ((wordIndex (champLen C) (one_le_champLen C) j : ℝ) + 1) := by
  set N := wordIndex (champLen C) (one_le_champLen C) j with hN
  obtain ⟨h1, h2⟩ := cum_le_wordIndex C j
  rw [← hN] at h1 h2
  have hd := drift_total C hC N
  have ho := (occ_cum_le C [true] N).1.trans (occ_mono (collatzChampernowne C) [true] h1)
  have ha := (occ_cum_le C (altWord 4) N).1.trans (occ_mono (collatzChampernowne C) (altWord 4) h1)
  have hoR : (interior C (fun s => [true].getD s false) [true].length N : ℝ) ≤
      occ (collatzChampernowne C) [true] j := by exact_mod_cast ho
  have haR : (interior C (fun s => (altWord 4).getD s false) (altWord 4).length N : ℝ) ≤
      occ (collatzChampernowne C) (altWord 4) j := by exact_mod_cast ha
  have hs : Nat.size (N + 1) ≤ N + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have hlen : j ≤ cum (champLen C) N + C * (N + 1) := by
    rw [cum_succ, champLen, max_eq_left (by omega : 1 ≤ C)] at h2
    have := Nat.mul_le_mul_left C hs
    omega
  have hlenR : (j : ℝ) ≤ cum (champLen C) N + C * ((N : ℝ) + 1) := by exact_mod_cast hlen
  have hNR : (0 : ℝ) ≤ N := by positivity
  have hCR : (0 : ℝ) ≤ C := by positivity
  nlinarith

/-- **Above the threshold, `𝒞_C` is not normal even in logarithmic density.**  `drift_total` holds at
every word end, and partial summation carries the linear inequality to logarithmic frequencies, whose
limit would again read `0.5 ≤ 0.4966`. -/
theorem not_logNormal_of_five_le (C : ℕ) (hC : 5 ≤ C) : ¬ LogNormal (collatzChampernowne C) := by
  intro hL
  set w := collatzChampernowne C with hw
  set D : ℝ := 34.03 + 0.8 * C with hD
  have hD0 : 0 ≤ D := by positivity
  set W := wordIndex (champLen C) (one_le_champLen C) with hWdef
  set y : ℕ → ℝ := fun i => 0.8 - 1.59 * occInd w [true] i - 0.41 * occInd w (altWord 4) i with hy
  have hsumy : ∀ k : ℕ, ∑ i ∈ Finset.range k, y i ≤ D * ((W k : ℝ) + 1) := fun k => by
    have e : ∑ i ∈ Finset.range k, y i =
        0.8 * (k : ℝ) - 1.59 * (occ w [true] k : ℝ) - 0.41 * (occ w (altWord 4) k : ℝ) := by
      simp only [hy, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_occInd]
      simp
      ring
    rw [e]
    exact drift_at C hC k
  have hpart : ∀ P : ℕ, ∑ i ∈ Finset.range P, y i / ((i : ℝ) + 1) ≤
      D * (((W P : ℝ) + 1) / ((P : ℝ) + 1)) + ∑ j ∈ Finset.range P,
        (D * (((W (j + 1) : ℝ) + 1) / ((j : ℝ) + 2))) / ((j : ℝ) + 1) := fun P => by
    rw [partial_sum y P]
    refine add_le_add ?_ (Finset.sum_le_sum fun j _ => ?_)
    · rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hsumy P) (by positivity)
    · refine div_le_div_of_nonneg_right ?_ (by positivity)
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hsumy (j + 1)) (by positivity)
  have hr : Tendsto (fun j : ℕ => D * (((W (j + 1) : ℝ) + 1) / ((j : ℝ) + 2))) atTop (𝓝 0) := by
    have h0 := (tendsto_wordIndex_div C).comp (tendsto_add_atTop_nat 1)
    have h1 : Tendsto (fun j : ℕ => ((W (j + 1) : ℝ) + 1) / ((j : ℝ) + 2)) atTop (𝓝 0) := by
      refine squeeze_zero (fun j => by positivity) (fun j => ?_) h0
      simp only [Function.comp]
      push_cast
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    simpa using h1.const_mul D
  have hR := (tendsto_bdd_div_log (fun P => D * (((W P : ℝ) + 1) / ((P : ℝ) + 1))) D fun P => by
    have h1 : (W P : ℝ) ≤ P := by exact_mod_cast wordIndex_le C P
    have h2 : ((W P : ℝ) + 1) / ((P : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h3 : 0 ≤ ((W P : ℝ) + 1) / ((P : ℝ) + 1) := by positivity
    rw [abs_of_nonneg (by positivity)]
    nlinarith).add (tendsto_log_mean_zero_of_tendsto _ hr)
  have h1 := (hL [true]).const_mul (1.59 : ℝ)
  have h2 := (hL (altWord 4)).const_mul (0.41 : ℝ)
  have hLHS := ((tendsto_harm_div_log.const_mul (0.8 : ℝ)).sub h1).sub h2
  have hle := le_of_tendsto_of_tendsto hLHS hR ?_
  · rw [length_altWord] at hle
    norm_num at hle
  · filter_upwards [tendsto_log_nat.eventually_gt_atTop 0] with P hP
    have e : ∑ i ∈ Finset.range P, y i / ((i : ℝ) + 1) =
        0.8 * (∑ i ∈ Finset.range P, 1 / ((i : ℝ) + 1)) - 1.59 * logSum w [true] P -
          0.41 * logSum w (altWord 4) P := by
      simp only [logSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [hy]; ring
    have hp := hpart P
    rw [e] at hp
    simp only [logFreq_eq]
    rw [← add_div, mul_div_assoc', mul_div_assoc', mul_div_assoc', ← sub_div, ← sub_div]
    exact div_le_div_of_nonneg_right hp hP.le

end CollatzMoonshot.Conjugacy
