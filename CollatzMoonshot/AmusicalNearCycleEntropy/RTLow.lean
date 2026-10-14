/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycleEntropy.Stopped
import CollatzMoonshot.AmusicalNearCycleEntropy.Estimates

/-!
# RT-low: the assembly

`L = log₂ D ≥ 1000`, `τ = ⌈L/4⌉`, `m = ⌊L/40⌋`, `M = ⌊141 τ / 100⌋ + 4`, `N = ⌊D L^14⌋`.  A deep
run-poor start `p ≤ N` is either `≤ L` (`3 eRuns ≥ 2p`) or follows a branch word over a stopped
prefix in `SP τ m M` (`exists_stopped`; the `O`-count is `≤ M` by P2′).  The fibers give
`#(main) ≤ N · NB + 2^M · #SP` (`card_fibers_le`), and `Estimates` turns each term into
`O(D^0.87)`.  Below `L = 1000` the set is bounded by `2^1000 · 1000^14 + 1`.
-/

namespace CollatzMoonshot.Amusical.NearCycleEntropy

open Finset

/-- The starts in `[0, N]` following the branch word `k`. -/
def fiber (N : ℕ) (k : List ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun p : ℕ => key k.length (p : ℤ) = k

/-- **The fiber count over stopped prefixes.** -/
theorem card_fibers_le (t m M N : ℕ) :
    (((SP (t + 1) m M).biUnion fun s => (lifts s).biUnion (fiber N)).card : ℝ) ≤
      N * ∑ j ∈ range m, (t.choose j : ℝ) / 2 ^ (t + 1) +
        2 ^ M * ∑ i ∈ range m, ((t.choose i * M.choose i : ℕ) : ℝ) := by
  have h1 : (((SP (t + 1) m M).biUnion fun s => (lifts s).biUnion (fiber N)).card : ℝ) ≤
      ∑ s ∈ SP (t + 1) m M, ∑ k ∈ lifts s, ((N : ℝ) / 2 ^ wt k + 1) := by
    have := (card_biUnion_le (s := SP (t + 1) m M)
      (t := fun s => (lifts s).biUnion (fiber N))).trans
      (sum_le_sum fun s _ => (card_biUnion_le (s := lifts s) (t := fiber N)).trans
        (sum_le_sum fun k _ => card_fiber_le N k))
    refine (Nat.cast_le.mpr this).trans ?_
    push_cast
    refine sum_le_sum fun s _ => sum_le_sum fun k _ => ?_
    have := Nat.cast_div_le (α := ℝ) (m := N) (n := 2 ^ wt k)
    push_cast at this
    linarith
  have h2 : ∀ s ∈ SP (t + 1) m M, ∑ k ∈ lifts s, ((N : ℝ) / 2 ^ wt k + 1) ≤
      N * ((1 : ℝ) / 2) ^ s.length + 2 ^ M := by
    intro s hs
    rw [sum_add_distrib, sum_const, nsmul_one]
    have hN : ∑ k ∈ lifts s, (N : ℝ) / 2 ^ wt k = N * ∑ k ∈ lifts s, ((1 : ℝ) / 2) ^ wt k := by
      rw [mul_sum]; refine sum_congr rfl fun k _ => ?_; rw [div_pow, one_pow]; ring
    rw [hN]
    have hc : ((lifts s).card : ℝ) ≤ 2 ^ M := by
      have := (card_lifts_le s).trans (Nat.pow_le_pow_right (by norm_num) (mem_SP.mp hs).2.2.2.1)
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_left (sum_lifts_le s) (Nat.cast_nonneg (α := ℝ) N)
    linarith
  refine h1.trans ((sum_le_sum h2).trans ?_)
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
  have hNB := mul_le_mul_of_nonneg_left (sum_SP_le t m M) (Nat.cast_nonneg (α := ℝ) N)
  have hcard : ((SP (t + 1) m M).card : ℝ) ≤
      ∑ i ∈ range m, ((t.choose i * M.choose i : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast card_SP_le t m M
  have := mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ 2 ^ M)
  linarith

/-- The two binomial terms. -/
theorem nb_le (t m : ℕ) :
    ∑ j ∈ range m, (t.choose j : ℝ) / 2 ^ (t + 1) ≤ 9 ^ m * (5 / 9) ^ (t + 1) := by
  rw [← sum_div, div_le_iff₀ (by positivity)]
  refine (sum_choose_lt_le t m).trans ?_
  rw [show (9 : ℝ) ^ m * (5 / 9) ^ (t + 1) * 2 ^ (t + 1) = 9 ^ m * (10 / 9) ^ t * (10 / 9) by
    rw [pow_succ, pow_succ, show (10 : ℝ) / 9 = 5 / 9 * 2 by norm_num, mul_pow]; ring]
  have : (0 : ℝ) ≤ 9 ^ m * (10 / 9) ^ t := by positivity
  nlinarith

theorem cnt_le (t m M : ℕ) :
    ∑ i ∈ range m, ((t.choose i * M.choose i : ℕ) : ℝ) ≤ 81 ^ m * (10 / 9) ^ (t + 1 + M) := by
  have h1 : ∑ i ∈ range m, ((t.choose i * M.choose i : ℕ) : ℝ) ≤
      (∑ i ∈ range m, (t.choose i : ℝ)) * ∑ i ∈ range m, (M.choose i : ℝ) := by
    rw [sum_mul]
    refine sum_le_sum fun i hi => ?_
    push_cast
    exact mul_le_mul_of_nonneg_left
      (single_le_sum (f := fun i => (M.choose i : ℝ)) (fun _ _ => by positivity) hi)
      (by positivity)
  refine h1.trans ((mul_le_mul (sum_choose_lt_le t m) (sum_choose_lt_le M m)
    (sum_nonneg fun _ _ => by positivity) (by positivity)).trans ?_)
  rw [show (81 : ℝ) = 9 * 9 by norm_num, mul_pow, pow_add, pow_succ]
  have : (0 : ℝ) ≤ 9 ^ m * 9 ^ m * (10 / 9) ^ t * (10 / 9) ^ M := by positivity
  nlinarith

/-- **RT-low.** -/
theorem ncard_deep_lowRun_le' :
    ∃ C : ℝ, ∀ D : ℕ, 2 ≤ D →
      (({p : ℕ | (p : ℝ) ≤ D * Real.logb 2 D ^ 14 ∧ ∃ g, NearCycleAt D p g ∧
          0.61 * Real.logb 2 D < g ∧ (eRuns p g : ℝ) ≤ Real.logb 2 D / 40}).ncard : ℝ) ≤
        C * (D : ℝ) ^ (0.87 : ℝ) := by
  obtain ⟨K0, hK0⟩ := logb_add_one_le
  obtain ⟨K1, hK1⟩ := main_le
  obtain ⟨K2, hK2⟩ := tail_le
  refine ⟨(2 : ℝ) ^ (1000 : ℝ) * 1000 ^ 14 + 1 + |K0| + |K1| + |K2|, fun D hD => ?_⟩
  set S := {p : ℕ | (p : ℝ) ≤ D * Real.logb 2 D ^ 14 ∧ ∃ g, NearCycleAt D p g ∧
          0.61 * Real.logb 2 D < g ∧ (eRuns p g : ℝ) ≤ Real.logb 2 D / 40} with hS
  set L := Real.logb 2 (D : ℝ) with hLdef
  have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hD87 : 1 ≤ (D : ℝ) ^ (0.87 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hD87' : 0 < (D : ℝ) ^ (0.87 : ℝ) := by linarith
  have hL1 : 1 ≤ L := one_le_logb hDR
  set N := ⌊(D : ℝ) * L ^ 14⌋₊ with hN
  have hNle : (N : ℝ) ≤ D * L ^ 14 := Nat.floor_le (by positivity)
  have habs : ∀ K : ℝ, ∀ x : ℝ, x ≤ K * (D : ℝ) ^ (0.87 : ℝ) → x ≤ |K| * (D : ℝ) ^ (0.87 : ℝ) :=
    fun K x h => h.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hD87'.le)
  have hK0' := habs _ _ (hK0 D hDR)
  have hC0 : (0 : ℝ) ≤ |K0| * (D : ℝ) ^ (0.87 : ℝ) := by positivity
  have hC1 : (0 : ℝ) ≤ |K1| * (D : ℝ) ^ (0.87 : ℝ) := by positivity
  have hC2 : (0 : ℝ) ≤ |K2| * (D : ℝ) ^ (0.87 : ℝ) := by positivity
  have hbig : (0 : ℝ) ≤ (2 : ℝ) ^ (1000 : ℝ) * 1000 ^ 14 + 1 := by positivity
  rw [add_mul, add_mul, add_mul]
  by_cases hL : L < 1000
  · -- small `D`
    have hsub : S ⊆ ↑(range (N + 1)) := by
      intro p hp
      simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.le_floor hp.1)
    have hcard : (S.ncard : ℝ) ≤ N + 1 := by
      have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset, card_range] at this
      exact_mod_cast this
    have hD2 : (D : ℝ) ≤ (2 : ℝ) ^ (1000 : ℝ) := by
      rw [← Real.rpow_logb (b := 2) (by norm_num) (by norm_num) (by linarith : (0 : ℝ) < D),
        ← hLdef]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hL.le
    have hL14 : L ^ 14 ≤ 1000 ^ 14 := pow_le_pow_left₀ (by linarith) hL.le 14
    have : (D : ℝ) * L ^ 14 ≤ (2 : ℝ) ^ (1000 : ℝ) * 1000 ^ 14 :=
      mul_le_mul hD2 hL14 (by positivity) (by positivity)
    have hkey : (S.ncard : ℝ) ≤ (2 : ℝ) ^ (1000 : ℝ) * 1000 ^ 14 + 1 :=
      hcard.trans (add_le_add_left (hNle.trans this) 1)
    have := le_mul_of_one_le_right hbig hD87
    generalize (2 : ℝ) ^ (1000 : ℝ) * 1000 ^ 14 + 1 = B0 at hkey this ⊢
    linarith
  push Not at hL
  -- large `D`
  set τ := ⌈L / 4⌉₊ with hτdef
  set m := ⌊L / 40⌋₊ with hmdef
  set M := 141 * τ / 100 + 4 with hMdef
  have hτ1 : L / 4 ≤ τ := Nat.le_ceil _
  have hτ2 : (τ : ℝ) < L / 4 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hm : (m : ℝ) ≤ L / 40 := Nat.floor_le (by linarith)
  have hM : (M : ℝ) ≤ 1.41 * τ + 4 := by
    have := Nat.cast_div_le (α := ℝ) (m := 141 * τ) (n := 100)
    rw [hMdef]; push_cast at this ⊢; linarith
  have hτpos : 1 ≤ τ := by
    have : (1 : ℝ) ≤ τ := by linarith
    exact_mod_cast this
  obtain ⟨t, ht⟩ : ∃ t, τ = t + 1 := ⟨τ - 1, by omega⟩
  have hLD : L / 40 ≤ D := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < D)
    have h2 : Real.log 2 > 0.69 := by linarith [Real.log_two_gt_d9]
    have : L * Real.log 2 = Real.log D := by
      rw [hLdef, Real.logb, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
    nlinarith
  set F := (SP τ m M).biUnion fun s => (lifts s).biUnion (fiber N)
  have hsub : S ⊆ ↑(range (⌊L⌋₊ + 1) ∪ F) := by
    rintro p ⟨hpY, g, hNC, hg, hmg⟩
    rw [coe_union, Set.mem_union]
    by_cases hsmall : 2 * p ≤ 3 * eRuns p g
    · left
      simp only [coe_range, Set.mem_Iio]
      refine Nat.lt_succ_of_le (Nat.le_floor ?_)
      have : (2 * p : ℝ) ≤ 3 * eRuns p g := by exact_mod_cast hsmall
      linarith
    right
    have hge := nearCycleAt_numE_ge hNC (by omega)
    have hθ : Real.logb 2 3 ≤ 317 / 200 := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]; linarith [log_theta]
    have hgR : (0.61 : ℝ) * L < g := hg
    have hτE : τ ≤ numE p g := by
      have : (τ : ℝ) ≤ numE p g := by nlinarith
      exact_mod_cast this
    have hmD : eRuns p g ≤ p + D := by
      have : (eRuns p g : ℝ) ≤ p + D := by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
      exact_mod_cast this
    obtain ⟨t', -, hh, hl, hct, hr, hB⟩ := exists_stopped hNC hτpos hτE hmD
    have hBM : (pat (t' + 1) (p : ℤ)).count false ≤ M := by
      have hb := log_beta
      have hq := quarter_le_log
      have hτR : (1 : ℝ) ≤ τ := by exact_mod_cast hτpos
      set B := (pat (t' + 1) (p : ℤ)).count false
      have hB' : (100 * B : ℝ) < 141 * τ + 259 := by
        by_contra hc
        push Not at hc
        nlinarith
      have : 100 * B < 141 * τ + 259 := by exact_mod_cast hB'
      omega
    have hs : pat (t' + 1) (p : ℤ) ∈ SP τ m M :=
      mem_SP.mpr ⟨hh, hl, hct, hBM, hr.trans (Nat.le_floor hmg)⟩
    rw [mem_coe, mem_biUnion]
    refine ⟨_, hs, mem_biUnion.mpr ⟨_, key_mem_lifts (t' + 1) p, ?_⟩⟩
    rw [fiber, mem_filter, mem_range, length_key]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpY), rfl⟩
  have hcard : (S.ncard : ℝ) ≤ (⌊L⌋₊ + 1 : ℝ) + F.card := by
    have := (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans_eq (Set.ncard_coe_finset _)
    have := this.trans (card_union_le _ _)
    rw [card_range] at this
    exact_mod_cast this
  have hF := card_fibers_le t m M N
  rw [show SP (t + 1) m M = SP τ m M by rw [ht]] at hF
  rw [← hLdef] at hK0'
  have hfl : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le (by linarith)
  have h1 : (N : ℝ) * ∑ j ∈ range m, (t.choose j : ℝ) / 2 ^ (t + 1) ≤
      |K1| * (D : ℝ) ^ (0.87 : ℝ) := by
    refine habs _ _ ((mul_le_mul hNle (nb_le t m) (sum_nonneg fun _ _ => by positivity)
      (by positivity)).trans ?_)
    rw [← ht, ← mul_assoc]
    exact hK1 D hDR τ m hτ1 hm
  have h2 : (2 : ℝ) ^ M * ∑ i ∈ range m, ((t.choose i * M.choose i : ℕ) : ℝ) ≤
      |K2| * (D : ℝ) ^ (0.87 : ℝ) := by
    refine habs _ _ ((mul_le_mul_of_nonneg_left (cnt_le t m M) (by positivity)).trans ?_)
    rw [← ht, ← mul_assoc]
    exact hK2 D hDR τ m M hτ2.le hm hM
  have := le_mul_of_one_le_right hbig hD87
  generalize (2 : ℝ) ^ (1000 : ℝ) * 1000 ^ 14 + 1 = B0 at hbig this ⊢
  linarith

end CollatzMoonshot.Amusical.NearCycleEntropy
