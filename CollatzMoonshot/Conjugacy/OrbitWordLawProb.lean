/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawOrbit
import TaoCollatz.Sec3.Reduction

/-!
# The orbit word law: the probabilistic side

Open nodes are `Prop`s here, with their `sorry`s in `OrbitWordLaw.lean`.

`winLaw x` is Tao's log-uniform law on the odd numbers in `[x^α, x^(α²)]`.

* **Terras, with constraints** (`CardMatchSet`): among `r < 2^m`, prescribing the letters at any
  set `S` of positions below `m` leaves `2^(m − |S|)` of them.
* **Chebyshev on a block** (`SumSqWdevLe`, `CardBadBlockLe`): occurrences of `u` at positions
  at least `|u|` apart are uncorrelated, so the second moment of the count over a block of `b`
  start positions is at most `2 |u| b` per residue.
* **Blocks give windows** (`WinGoodOfBlocks`): a deviation is `1`-Lipschitz in the end point, so
  good blocks of length `b ≤ δ H / 8` make every window of length `≥ H` good.  Boundedly many
  blocks cover the first `2 Λ` letters, so `¬ WinGood` has probability `O(1 / (δ² η log x))`
  over residues (`WinGoodWhp`).
* **Transfer** (`ProbPeriodicLe`): an event that only sees `N mod 2^(3 n₀)` has nearly the same
  probability under `winLaw x` as over odd residues, by Tao's integral test.
* **The chain** (`dTV_chain`): by Tao's Proposition 1.11 at each scale, data processing, and
  `passLoc_passLoc`, the law of the passage location below `x_j` of a start drawn from `winLaw x`
  is close to that of a start drawn from `winLaw x_j`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-- Tao's window law at scale `x`: log-uniform on the odd numbers in `[x^α, x^(α²)]`. -/
noncomputable def winLaw (x : ℝ) : PMF ℕ := logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)

/-! ## Event probabilities -/

/-- An event probability is nonnegative. -/
theorem prob_nonneg (p : PMF ℕ) (A : Set ℕ) : 0 ≤ p.expect (Set.indicator A 1) :=
  tsum_nonneg fun n => mul_nonneg ENNReal.toReal_nonneg
    (Set.indicator_nonneg (fun _ _ => zero_le_one) n)

/-- Monotonicity on the support. -/
theorem prob_mono_support (p : PMF ℕ) {A B : Set ℕ} (h : ∀ n ∈ p.support, n ∈ A → n ∈ B) :
    p.expect (Set.indicator A 1) ≤ p.expect (Set.indicator B 1) := by
  unfold PMF.expect
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_indicator_term p A)
    (summable_indicator_term p B)
  by_cases hn : n ∈ p.support
  · by_cases hA : n ∈ A
    · simp [hA, h n hn hA]
    · simp only [Set.indicator_of_notMem hA, mul_zero]
      exact mul_nonneg ENNReal.toReal_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) n)
  · rw [PMF.mem_support_iff, not_not] at hn
    simp [hn]

/-- The union bound over a finite family. -/
theorem prob_biUnion_le {ι : Type*} (p : PMF ℕ) (s : Finset ι) (B : ι → Set ℕ) :
    p.expect (Set.indicator (⋃ j ∈ s, B j) 1) ≤ ∑ j ∈ s, p.expect (Set.indicator (B j) 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PMF.expect]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.set_biUnion_insert]
    exact le_trans (expect_indicator_union_le p _ _) (by linarith [ih])

/-- **The union bound**, on the support. -/
theorem prob_le_sum {ι : Type*} (p : PMF ℕ) (A : Set ℕ) (s : Finset ι) (B : ι → Set ℕ)
    (h : ∀ n ∈ p.support, n ∈ A → ∃ j ∈ s, n ∈ B j) :
    p.expect (Set.indicator A 1) ≤ ∑ j ∈ s, p.expect (Set.indicator (B j) 1) := by
  refine le_trans (prob_mono_support p (B := ⋃ j ∈ s, B j) fun n hn hA => ?_)
    (prob_biUnion_le p s B)
  obtain ⟨j, hj, hjB⟩ := h n hn hA
  exact Set.mem_biUnion hj hjB

/-- For large `x`, the support of `winLaw x` is odd and inside `[x^α, x^(α²)]`. -/
theorem winLaw_support {x : ℝ} (hx : X_windowBase ≤ x) {n : ℕ} (hn : n ∈ (winLaw x).support) :
    n % 2 = 1 ∧ x ^ alpha ≤ n ∧ (n : ℝ) ≤ x ^ alpha ^ 2 := by
  have hx0 : 0 ≤ x := le_trans (by unfold X_windowBase X_nZeroPos; positivity) hx
  have hpow : (x ^ alpha) ^ alpha = x ^ alpha ^ 2 := by rw [← Real.rpow_mul hx0, pow_two]
  have hne := logWindow_nonempty_atX x hx (x ^ alpha) (Set.mem_insert _ _)
  rw [hpow] at hne
  unfold winLaw logUnifOdd at hn
  rw [dif_pos hne, PMF.mem_support_ofFinset_iff] at hn
  have hw := hn.1
  simp only [logWindow, Finset.mem_filter] at hw
  exact ⟨hw.2.1, hw.2.2.1, hw.2.2.2⟩

/-! ## Terras with constraints, and Chebyshev on a block -/

/-- **Node: Terras, with constraints.**  Prescribing the letters at the positions of `S ⊆ [0, m)` leaves
exactly `2^(m − |S|)` of the residues `r < 2^m`. -/
def CardMatchSet : Prop :=
  ∀ (g : ℕ → Bool) (S : Finset ℕ) (m : ℕ), (∀ s ∈ S, s < m) →
    ((Finset.range (2 ^ m)).filter fun r => ∀ s ∈ S, accWord r s = g s).card = 2 ^ (m - S.card)

/-- Node.  One window: `2^(m − |u|)` residues match `u` at `i`, when `i + |u| ≤ m`. -/
def CardMatchOne : Prop :=
  ∀ (u : List Bool) (m i : ℕ), i + u.length ≤ m →
    ((Finset.range (2 ^ m)).filter
      fun r => WindowMatch (fun s => u.getD s false) u.length i r).card = 2 ^ (m - u.length)

/-- Node.  Two disjoint windows: `2^(m − 2|u|)` residues match `u` at both `i` and `i'`, when
`i + |u| ≤ i'` and `i' + |u| ≤ m`. -/
def CardMatchTwo : Prop :=
  ∀ (u : List Bool) (m i i' : ℕ), i + u.length ≤ i' → i' + u.length ≤ m →
    ((Finset.range (2 ^ m)).filter fun r =>
      WindowMatch (fun s => u.getD s false) u.length i r ∧
        WindowMatch (fun s => u.getD s false) u.length i' r).card = 2 ^ (m - 2 * u.length)

/-- **Node: the second moment over a block.**  For `a + b + |u| ≤ m`,
`∑_{r < 2^m} wdev(r)² ≤ 2 |u| b 2^m`. -/
def SumSqWdevLe : Prop :=
  ∀ (u : List Bool) (m a b : ℕ), a + b + u.length ≤ m →
    ∑ r ∈ Finset.range (2 ^ m), (wdev u r a b) ^ 2 ≤ 2 * u.length * b * 2 ^ m

/-- **Node: Chebyshev on a block.** -/
def CardBadBlockLe : Prop :=
  ∀ (u : List Bool) (m a b : ℕ) (ε : ℝ), a + b + u.length ≤ m → 0 < ε → 0 < b →
    (((Finset.range (2 ^ m)).filter fun r => ε * b < |wdev u r a b|).card : ℝ) ≤
      2 * u.length * 2 ^ m / (ε ^ 2 * b)

/-- **Node: blocks give windows.**  If the `K` blocks `[k b, (k + 1) b)` are good within `δ / 4`, with
`K b ≥ 2 Λ` and `8 b ≤ δ H`, then every window at offset `≤ Λ` with length in `[H, Λ]` is good
within `δ`. -/
def WinGoodOfBlocks : Prop :=
  ∀ (u : List Bool) (δ : ℝ) (H Λ K b n : ℕ), 0 < δ → 0 < b → 2 * Λ ≤ K * b →
    8 * (b : ℝ) ≤ δ * H → (∀ k < K, |wdev u n (k * b) b| ≤ δ / 4 * b) → WinGood u δ H Λ n

/-- Node.  A window event sees only `N mod 2^m`, when `2 Λ + |u| ≤ m`. -/
def WinGoodModIff : Prop :=
  ∀ (u : List Bool) (δ : ℝ) (H Λ m : ℕ), 2 * Λ + u.length ≤ m →
    ∀ n : ℕ, WinGood u δ H Λ (n % 2 ^ m) ↔ WinGood u δ H Λ n

open Classical in
/-- **Node: transfer by the integral test.**  For large `x`, an event that sees only `N mod 2^m`,
`m = 3 n₀(x)`, has `winLaw x`-probability at most twice its proportion among residues, plus
`K 2^(−m)`. -/
def ProbPeriodicLe : Prop :=
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → ∀ S : Set ℕ, (∀ n, n % 2 ^ (3 * nZero x) ∈ S ↔ n ∈ S) →
      (winLaw x).expect (Set.indicator S 1) ≤
        2 * (((Finset.range (2 ^ (3 * nZero x))).filter (· ∈ S)).card : ℝ) / 2 ^ (3 * nZero x) +
          K_intTest * (2 : ℝ) ^ (-(3 * (nZero x : ℝ)))

/-- **Node: Terras at one scale.**  Under `winLaw x`, all windows of the first `2 lam x` letters are good,
with probability tending to `1`. -/
def WinGoodWhp : Prop :=
  ∀ (u : List Bool) (δ η : ℝ), 0 < δ → 0 < η →
    Tendsto (fun x => (winLaw x).expect
      (Set.indicator {N | ¬ WinGood u δ (hgt η x) (lam x) N} 1)) atTop (𝓝 0)

/-- Both words at one scale. -/
theorem scaleGood_whp (hW : WinGoodWhp) (u : List Bool) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    Tendsto (fun x => (winLaw x).expect
      (Set.indicator {N | ¬ ScaleGood u δ η x N} 1)) atTop (𝓝 0) := by
  have hsum := (hW u δ η hδ hη).add (hW [true] (1 / 100) η (by norm_num) hη)
  rw [add_zero] at hsum
  refine squeeze_zero (fun x => prob_nonneg _ _) (fun x => ?_) hsum
  refine le_trans (prob_mono_support _ (B := {N | ¬ WinGood u δ (hgt η x) (lam x) N} ∪
    {N | ¬ WinGood [true] (1 / 100) (hgt η x) (lam x) N}) fun n _ hn => ?_)
    (expect_indicator_union_le _ _ _)
  simp only [ScaleGood, Set.mem_ofPred_eq, not_and_or] at hn
  exact hn

/-- **The location event.**  Under `ν_x`, the law of the passage location below `x` of a start
drawn from `winLaw x`, the location is good at scale `x` with probability tending to `1`. -/
theorem locGood_whp (hW : WinGoodWhp) (hL : LocGoodPassLoc) (u : List Bool) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hη1 : η ≤ 1 / 1000) :
    Tendsto (fun x => ((winLaw x).map (passLoc ⌊x⌋₊)).expect
      (Set.indicator {M | ¬ LocGood u δ η x M} 1)) atTop (𝓝 0) := by
  obtain ⟨X₀, hX₀⟩ := hL u δ η hη hη1
  refine squeeze_zero' (Eventually.of_forall fun x => prob_nonneg _ _) ?_
    (scaleGood_whp hW u hδ hη)
  filter_upwards [eventually_ge_atTop (max X₀ X_windowBase)] with x hx
  rw [expect_indicator_map]
  refine prob_mono_support _ fun n hn hbad => ?_
  obtain ⟨hodd, -, hhi⟩ := winLaw_support (le_trans (le_max_right _ _) hx) hn
  intro hsg
  exact hbad (hX₀ x (le_trans (le_max_left _ _) hx) n hodd hhi hsg)

/-! ## The chain of scales -/

/-- The scales tend to infinity. -/
theorem tendsto_scale (j : ℕ) : Tendsto (fun x => scale x j) atTop atTop := by
  exact tendsto_rpow_atTop (pow_pos (inv_pos.mpr (by norm_num [alpha])) j)

/-- The triangle inequality for `dTV`. -/
theorem dTV_triangle (p q r : PMF ℕ) : p.dTV r ≤ p.dTV q + q.dTV r := by
  have hs : ∀ a b : PMF ℕ, Summable fun n => |(a n).toReal - (b n).toReal| := by
    intro a b
    have ha : Summable fun n => (a n).toReal := ENNReal.summable_toReal a.tsum_coe_ne_top
    have hb : Summable fun n => (b n).toReal := ENNReal.summable_toReal b.tsum_coe_ne_top
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) (ha.add hb)
    have h1 : 0 ≤ (a n).toReal := ENNReal.toReal_nonneg
    have h2 : 0 ≤ (b n).toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  unfold PMF.dTV
  rw [← Summable.tsum_add (hs p q) (hs q r)]
  exact Summable.tsum_le_tsum (fun n => abs_sub_le _ _ _) (hs p r) ((hs p q).add (hs q r))

/-- `dTV p p = 0`. -/
theorem dTV_self (p : PMF ℕ) : p.dTV p = 0 := by
  simp [PMF.dTV]

/-- One link of the chain: for large `x`, the distance at scale `j + 1` is at most the distance at
scale `j` plus Proposition 1.11 at `x_(j+1)`. -/
theorem dTV_chain_step (j : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : 1 ≤ scale x (j + 1))
    (hxs : X_stab ≤ scale x (j + 1)) :
    PMF.dTV ((winLaw x).map (passLoc ⌊scale x (j + 1)⌋₊))
        ((winLaw (scale x (j + 1))).map (passLoc ⌊scale x (j + 1)⌋₊)) ≤
      PMF.dTV ((winLaw x).map (passLoc ⌊scale x j⌋₊))
        ((winLaw (scale x j)).map (passLoc ⌊scale x j⌋₊)) +
      C_stab * (Real.log (scale x (j + 1))) ^ (-c_stab) := by
  set y := scale x (j + 1) with hydef
  have hy0 : 0 ≤ y := by linarith
  have hyj : y ^ alpha = scale x j := scale_succ_rpow hx0 j
  have hyy : y ≤ scale x j := by
    rw [← hyj]
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 (show (1 : ℝ) ≤ alpha by norm_num [alpha])
  have hfl1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hx1)
  have hfl : ⌊y⌋₊ ≤ ⌊scale x j⌋₊ := Nat.floor_le_floor hyy
  set f := passLoc ⌊y⌋₊ with hfdef
  set g := passLoc ⌊scale x j⌋₊ with hgdef
  have hfg : f ∘ g = f := funext fun N => passLoc_passLoc hfl1 hfl N
  have hmap : ∀ p : PMF ℕ, p.map f = (p.map g).map f := fun p => by
    rw [PMF.map_comp, hfg]
  have h1 : PMF.dTV ((winLaw x).map f) ((winLaw (scale x j)).map f) ≤
      PMF.dTV ((winLaw x).map g) ((winLaw (scale x j)).map g) := by
    rw [hmap (winLaw x), hmap (winLaw (scale x j))]
    exact PMF.dTV_map_le _ _ _
  have hw1 : winLaw (scale x j) = logUnifOdd (y ^ alpha ^ 2) (y ^ alpha ^ 3) := by
    rw [winLaw, ← hyj, ← Real.rpow_mul hy0, ← Real.rpow_mul hy0]
    congr 2 <;> ring
  have h2 : PMF.dTV ((winLaw (scale x j)).map f) ((winLaw y).map f) ≤
      C_stab * (Real.log y) ^ (-c_stab) := by
    rw [hw1, PMF.dTV_comm]
    exact (stabilization_atCX y hxs).2
  exact le_trans (dTV_triangle _ _ _) (add_le_add h1 h2)

/-- **The chain.**  The law of the passage location below `x_j` of a start drawn from `winLaw x` is
within `o(1)` of `ν_(x_j)`, by induction on `j`: Proposition 1.11 at `x_(j+1)`, data processing,
and `passLoc_passLoc`. -/
theorem dTV_chain (j : ℕ) :
    Tendsto (fun x => PMF.dTV ((winLaw x).map (passLoc ⌊scale x j⌋₊))
      ((winLaw (scale x j)).map (passLoc ⌊scale x j⌋₊))) atTop (𝓝 0) := by
  induction j with
  | zero =>
    have : ∀ x, scale x 0 = x := fun x => by simp [scale]
    simp only [this, dTV_self]
    exact tendsto_const_nhds
  | succ j ih =>
    have hlog : Tendsto (fun x => C_stab * (Real.log (scale x (j + 1))) ^ (-c_stab)) atTop
        (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop c_stab_pos).comp
        (Real.tendsto_log_atTop.comp (tendsto_scale (j + 1)))).const_mul C_stab
      simpa using this
    have hsum := ih.add hlog
    rw [add_zero] at hsum
    refine squeeze_zero' (Eventually.of_forall fun x => PMF.dTV_nonneg _ _) ?_ hsum
    filter_upwards [eventually_ge_atTop 0, (tendsto_scale (j + 1)).eventually_ge_atTop 1,
      (tendsto_scale (j + 1)).eventually_ge_atTop X_stab] with x hx0 hx1 hxs
    exact dTV_chain_step j hx0 hx1 hxs

/-- Each stage event holds with probability tending to `1`. -/
theorem stage_whp (hW : WinGoodWhp) (hL : LocGoodPassLoc) (u : List Bool) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hη1 : η ≤ 1 / 1000) (j : ℕ) :
    Tendsto (fun x => (winLaw x).expect (Set.indicator
      {n | ¬ LocGood u δ η (scale x j) (passLoc ⌊scale x j⌋₊ n)} 1)) atTop (𝓝 0) := by
  have h1 := (locGood_whp hW hL u hδ hη hη1).comp (tendsto_scale j)
  have h2 := (h1.add (dTV_chain j))
  rw [add_zero] at h2
  refine squeeze_zero (fun x => prob_nonneg _ _) (fun x => ?_) h2
  have hmap := expect_indicator_map (winLaw x) (passLoc ⌊scale x j⌋₊)
    {M | ¬ LocGood u δ η (scale x j) M}
  have hd := PMF.abs_expect_indicator_sub_le_dTV ((winLaw x).map (passLoc ⌊scale x j⌋₊))
    ((winLaw (scale x j)).map (passLoc ⌊scale x j⌋₊)) {M | ¬ LocGood u δ η (scale x j) M}
  have key : (winLaw x).expect
      ({n | ¬ LocGood u δ η (scale x j) (passLoc ⌊scale x j⌋₊ n)}.indicator 1) =
      ((winLaw x).map (passLoc ⌊scale x j⌋₊)).expect
        ({M | ¬ LocGood u δ η (scale x j) M}.indicator 1) := hmap.symm
  rw [key]
  simp only [Function.comp_apply]
  linarith [(abs_le.mp hd).2]

/-- **All scales at once.**  Under `winLaw x`, the start is good over its first `4.2 size n`
letters with probability tending to `1`. -/
theorem goodOdd_whp (hR : GoodOddOfStages) (hW : WinGoodWhp) (hL : LocGoodPassLoc)
    (u : List Bool) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x => (winLaw x).expect (Set.indicator {n | ¬ GoodOdd u δ n} 1))
      atTop (𝓝 0) := by
  obtain ⟨δ₀, η, X₀, hδ₀, hη, hη1, hread⟩ := hR u δ hδ
  have hsum := (scaleGood_whp hW u hδ₀ hη).add
    (tendsto_finsetSum (Finset.range numScales) fun j _ => stage_whp hW hL u hδ₀ hη hη1 j)
  rw [Finset.sum_const_zero, add_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun x => prob_nonneg _ _) ?_ hsum
  filter_upwards [eventually_ge_atTop (max X₀ X_windowBase)] with x hx
  refine le_trans (prob_mono_support _ (B := {N | ¬ ScaleGood u δ₀ η x N} ∪
    ⋃ j ∈ Finset.range numScales,
      {n | ¬ LocGood u δ₀ η (scale x j) (passLoc ⌊scale x j⌋₊ n)}) fun n hn hbad => ?_)
    (le_trans (expect_indicator_union_le _ _ _) (add_le_add le_rfl (prob_biUnion_le _ _ _)))
  obtain ⟨hodd, hlo, hhi⟩ := winLaw_support (le_trans (le_max_right _ _) hx) hn
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, not_or,
    not_exists, not_not] at hcon
  exact hbad (hread x (le_trans (le_max_left _ _) hx) n hodd hlo hhi hcon.1
    fun j hj => hcon.2 j hj)

end CollatzMoonshot.Conjugacy
