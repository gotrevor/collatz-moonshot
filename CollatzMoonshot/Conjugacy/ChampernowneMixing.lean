/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.ChampernowneOne

/-!
# Short-interval mixing makes `𝒞_C` normal

Write `defect C g L N` for the interior occurrences of the window `g` in the first `N` words of
`𝒞_C`, minus their expected number.  Inside stage `k` every word has `C k` letters, so the defect
of a run of `m` integers of the stage is a sum over the `C k` offsets (`defect_stage_eq`):

* offsets `t < k` cost `2^t` by Terras (`abs_card_Ico_windowMatch_sub_le`), `2^k` in all;
* offsets `t ≥ k` cost `δ 2^(k-1)` each by `ShortIntervalMixing C`, for `δ C k 2^(k-1)` in all.

Over the stages this gives `|defect N| ≤ E₀ + 4 (N + 1) + 2 δ C k (N + 1)` with `k = size (N + 1)`
(`abs_defect_le`).  Since `C (k − 1) (N + 1) ≤ 2 cum N` (`mul_size_le_two_cum`), the frequency error
is at most `8 δ` plus terms that vanish.  The hypothesis is used uniformly in `m`, because a prefix
may be cut anywhere inside a stage.

The converse only returns an average over positions: normality says the average over
`t ∈ [k, C k)` of the discrepancies vanishes, not each `t`.  That averaged converse is
`averagedMixing_of_normal` in `ChampernowneAveraged.lean`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- Interior occurrences in the first `N` words of `𝒞_C`, minus their expected number. -/
noncomputable def defect (C : ℕ) (g : ℕ → Bool) (L N : ℕ) : ℝ :=
  (interior C g L N : ℝ) - (windowCount C L N : ℝ) / 2 ^ L

/-- The window count of offset `t` over the first `m` integers of stage `k`, minus its expected
number. -/
noncomputable def stageError (g : ℕ → Bool) (L k t m : ℕ) : ℝ :=
  (((Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m)).filter (WindowMatch g L t)).card : ℝ) -
    (m : ℝ) / 2 ^ L

/-- The integers `2^(k-1) + x`, `x < 2^(k-1)`, have `k` bits. -/
private theorem size_stage (k x : ℕ) (hk : 1 ≤ k) (hx : x < 2 ^ (k - 1)) :
    Nat.size (2 ^ (k - 1) - 1 + x + 1) = k := by
  have hpos : 0 < 2 ^ (k - 1) := by positivity
  have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  apply le_antisymm
  · exact Nat.size_le.mpr (by omega)
  · have : k - 1 < Nat.size (2 ^ (k - 1) - 1 + x + 1) := Nat.lt_size.mpr (by omega)
    omega

/-- Inside stage `k`, every word of `𝒞_C` has `C k` letters. -/
private theorem champLen_stage (C : ℕ) (hC : 1 ≤ C) (k x : ℕ) (hk : 1 ≤ k) (hx : x < 2 ^ (k - 1)) :
    champLen C (2 ^ (k - 1) - 1 + x) = C * k := by
  rw [champLen, max_eq_left hC, size_stage k x hk hx]

/-- The interior count of `m` further integers of stage `k`, by offset. -/
private theorem interior_stage (C : ℕ) (hC : 1 ≤ C) (g : ℕ → Bool) (L k m : ℕ) (hk : 1 ≤ k)
    (hm : m ≤ 2 ^ (k - 1)) :
    interior C g L (2 ^ (k - 1) - 1 + m) = interior C g L (2 ^ (k - 1) - 1) +
      ∑ t ∈ (Finset.range (C * k)).filter (fun t => t + L ≤ C * k),
        ((Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m)).filter (WindowMatch g L t)).card := by
  have hpos : 0 < 2 ^ (k - 1) := by positivity
  unfold interior
  rw [Finset.sum_range_add]
  congr 1
  have h1 : ∀ x ∈ Finset.range m,
      ((Finset.range (champLen C (2 ^ (k - 1) - 1 + x))).filter fun i =>
        i + L ≤ champLen C (2 ^ (k - 1) - 1 + x) ∧
          WindowMatch g L i (2 ^ (k - 1) - 1 + x + 1)).card =
      ∑ t ∈ (Finset.range (C * k)).filter (fun t => t + L ≤ C * k),
        if WindowMatch g L t (2 ^ (k - 1) + x) then 1 else 0 := by
    intro x hx
    have hx' : x < 2 ^ (k - 1) := lt_of_lt_of_le (Finset.mem_range.mp hx) hm
    rw [champLen_stage C hC k x hk hx', ← Finset.filter_filter, Finset.card_filter]
    have he : 2 ^ (k - 1) - 1 + x + 1 = 2 ^ (k - 1) + x := by omega
    rw [he]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.card_filter, Finset.sum_Ico_eq_sum_range]
  simp

/-- The window count of `m` further integers of stage `k`. -/
private theorem windowCount_stage (C : ℕ) (hC : 1 ≤ C) (L k m : ℕ) (hk : 1 ≤ k)
    (hm : m ≤ 2 ^ (k - 1)) :
    windowCount C L (2 ^ (k - 1) - 1 + m) = windowCount C L (2 ^ (k - 1) - 1) +
      ((Finset.range (C * k)).filter (fun t => t + L ≤ C * k)).card * m := by
  unfold windowCount
  rw [Finset.sum_range_add]
  congr 1
  have h1 : ∀ x ∈ Finset.range m,
      ((Finset.range (champLen C (2 ^ (k - 1) - 1 + x))).filter fun i =>
        i + L ≤ champLen C (2 ^ (k - 1) - 1 + x)).card =
      ((Finset.range (C * k)).filter (fun t => t + L ≤ C * k)).card := by
    intro x hx
    rw [champLen_stage C hC k x hk (lt_of_lt_of_le (Finset.mem_range.mp hx) hm)]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

/-- Inside stage `k` all words have `C k` letters, so the defect of `m` further integers is a sum
over the offsets that fit. -/
theorem defect_stage_eq (C : ℕ) (hC : 1 ≤ C) (g : ℕ → Bool) (L k m : ℕ) (hk : 1 ≤ k)
    (hm : m ≤ 2 ^ (k - 1)) :
    defect C g L (2 ^ (k - 1) - 1 + m) - defect C g L (2 ^ (k - 1) - 1) =
      ∑ t ∈ (Finset.range (C * k)).filter (fun t => t + L ≤ C * k), stageError g L k t m := by
  have hI := interior_stage C hC g L k m hk hm
  have hW := windowCount_stage C hC L k m hk hm
  simp only [defect, stageError]
  rw [hI, hW, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- The offsets below `k` cost at most `2^k` in all, by Terras. -/
theorem abs_stage_sum_low_le (C : ℕ) (g : ℕ → Bool) (L k m : ℕ) :
    |∑ t ∈ ((Finset.range (C * k)).filter (fun t => t + L ≤ C * k)).filter (fun t => t < k),
        stageError g L k t m| ≤ 2 ^ k := by
  have hgeom : ∀ T : ℕ, ∑ t ∈ Finset.range T, (2 : ℝ) ^ t + 1 = 2 ^ T := by
    intro T
    induction T with
    | zero => simp
    | succ T ih => rw [Finset.sum_range_succ, pow_succ]; linarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ t ∈ ((Finset.range (C * k)).filter (fun t => t + L ≤ C * k)).filter (fun t => t < k),
        |stageError g L k t m|
      ≤ ∑ t ∈ ((Finset.range (C * k)).filter (fun t => t + L ≤ C * k)).filter (fun t => t < k),
          (2 : ℝ) ^ t :=
        Finset.sum_le_sum fun t _ => abs_card_Ico_windowMatch_sub_le g L t _ m
    _ ≤ ∑ t ∈ Finset.range k, (2 : ℝ) ^ t := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro t ht
        exact Finset.mem_range.mpr (Finset.mem_filter.mp ht).2
    _ ≤ 2 ^ k := by linarith [hgeom k]

/-- **One stage.**  Terras below offset `k`, the mixing hypothesis at and above it. -/
theorem abs_stage_sum_le (C : ℕ) (hC : 1 ≤ C) (g : ℕ → Bool) (L k m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hmix : ∀ t, k ≤ t → t + L ≤ C * k → |stageError g L k t m| ≤ δ * 2 ^ (k - 1)) :
    |∑ t ∈ (Finset.range (C * k)).filter (fun t => t + L ≤ C * k), stageError g L k t m| ≤
      2 ^ k + δ * (C * k) * 2 ^ (k - 1) := by
  set F := (Finset.range (C * k)).filter (fun t => t + L ≤ C * k) with hF
  have h1 : |∑ t ∈ F.filter (fun t => t < k), stageError g L k t m| ≤ 2 ^ k :=
    abs_stage_sum_low_le C g L k m
  have h2 : |∑ t ∈ F.filter (fun t => ¬ t < k), stageError g L k t m| ≤
      δ * (C * k) * 2 ^ (k - 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ t ∈ F.filter (fun t => ¬ t < k), |stageError g L k t m| ≤ δ * 2 ^ (k - 1) := by
      intro t ht
      have ht' := Finset.mem_filter.mp ht
      exact hmix t (not_lt.mp ht'.2) (Finset.mem_filter.mp ht'.1).2
    refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
    have hcard : (F.filter (fun t => ¬ t < k)).card ≤ C * k := by
      calc _ ≤ F.card := Finset.card_filter_le _ _
        _ ≤ (Finset.range (C * k)).card := Finset.card_filter_le _ _
        _ = C * k := Finset.card_range _
    have hcR : ((F.filter (fun t => ¬ t < k)).card : ℝ) ≤ C * k := by exact_mod_cast hcard
    rw [nsmul_eq_mul]
    have hX : (0 : ℝ) ≤ δ * 2 ^ (k - 1) := by positivity
    calc _ ≤ ((C : ℝ) * k) * (δ * 2 ^ (k - 1)) := mul_le_mul_of_nonneg_right hcR hX
      _ = _ := by ring
  rw [← Finset.sum_filter_add_sum_filter_not F (fun t => t < k)]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- The defect at the end of stage `k`, summed from stage `K`, given a bound on each stage sum. -/
theorem abs_defect_stage_end_le_of_stage (C : ℕ) (hC : 1 ≤ C) (g : ℕ → Bool) (L K : ℕ) (hK : 1 ≤ K)
    (δ : ℝ) (hδ : 0 < δ)
    (hstage : ∀ k, K ≤ k → ∀ m, m ≤ 2 ^ (k - 1) →
      |∑ t ∈ (Finset.range (C * k)).filter (fun t => t + L ≤ C * k), stageError g L k t m| ≤
        2 ^ k + δ * (C * k) * 2 ^ (k - 1))
    (k : ℕ) (hk : K ≤ k + 1) :
    |defect C g L (2 ^ k - 1)| ≤
      |defect C g L (2 ^ (K - 1) - 1)| + 2 ^ (k + 1) + δ * (C * k) * 2 ^ k := by
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  induction k with
  | zero =>
    have hK1 : K = 1 := by omega
    subst hK1
    simp
  | succ k ih =>
    rcases Nat.lt_or_ge (k + 1) K with hlt | hge
    · have hKe : K - 1 = k + 1 := by omega
      rw [hKe]
      have : (0 : ℝ) ≤ δ * (C * ((k + 1 : ℕ) : ℝ)) * 2 ^ (k + 1) := by positivity
      have h2 : (0 : ℝ) ≤ 2 ^ (k + 1 + 1) := by positivity
      linarith
    · have ih' := ih hge
      have hstage' := defect_stage_eq C hC g L (k + 1) (2 ^ k) (by omega) (by simp)
      have hsum := hstage (k + 1) hge (2 ^ k) (by simp)
      simp only [Nat.add_sub_cancel] at hstage' hsum
      have he : 2 ^ k - 1 + 2 ^ k = 2 ^ (k + 1) - 1 := by
        have : 0 < 2 ^ k := by positivity
        rw [pow_succ]; omega
      rw [he] at hstage'
      have htri : |defect C g L (2 ^ (k + 1) - 1)| ≤ |defect C g L (2 ^ k - 1)| +
          |defect C g L (2 ^ (k + 1) - 1) - defect C g L (2 ^ k - 1)| := by
        have := abs_add_le (defect C g L (2 ^ k - 1))
          (defect C g L (2 ^ (k + 1) - 1) - defect C g L (2 ^ k - 1))
        simpa using this
      rw [hstage'] at htri
      have hX : (0 : ℝ) ≤ δ * C * 2 ^ k := by positivity
      push_cast at hsum ⊢
      have e1 : δ * ((C : ℝ) * k) * 2 ^ k = δ * C * 2 ^ k * k := by ring
      have e2 : δ * ((C : ℝ) * (k + 1)) * 2 ^ k = δ * C * 2 ^ k * k + δ * C * 2 ^ k := by ring
      have e3 : δ * ((C : ℝ) * (k + 1)) * 2 ^ (k + 1) =
          2 * (δ * C * 2 ^ k * k) + 2 * (δ * C * 2 ^ k) := by ring
      have e4 : (2 : ℝ) ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      rw [e1] at ih'
      rw [e2] at hsum
      rw [e3, e4]
      linarith

/-- The defect at any word end at or beyond stage `K`, given a bound on each stage sum. -/
theorem abs_defect_le_of_stage (C : ℕ) (hC : 1 ≤ C) (g : ℕ → Bool) (L K : ℕ) (hK : 1 ≤ K)
    (δ : ℝ) (hδ : 0 < δ)
    (hstage : ∀ k, K ≤ k → ∀ m, m ≤ 2 ^ (k - 1) →
      |∑ t ∈ (Finset.range (C * k)).filter (fun t => t + L ≤ C * k), stageError g L k t m| ≤
        2 ^ k + δ * (C * k) * 2 ^ (k - 1))
    (N : ℕ) (hN : K ≤ Nat.size (N + 1)) :
    |defect C g L N| ≤
      |defect C g L (2 ^ (K - 1) - 1)| + 4 * ((N : ℝ) + 1) +
        2 * δ * (C * Nat.size (N + 1)) * ((N : ℝ) + 1) := by
  have hNpos : 0 < N + 1 := N.succ_pos
  have hsz : 1 ≤ Nat.size (N + 1) := Nat.size_pos.mpr hNpos
  obtain ⟨j, hj⟩ : ∃ j, Nat.size (N + 1) = j + 1 := ⟨Nat.size (N + 1) - 1, by omega⟩
  have hlo : 2 ^ j ≤ N + 1 := Nat.lt_size.mp (by omega)
  have hhi : N + 1 < 2 ^ (j + 1) := by
    rw [← hj]; exact Nat.lt_size_self _
  have hpos : 0 < 2 ^ j := by positivity
  have hdbl : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  obtain ⟨m, hm⟩ : ∃ m, N = 2 ^ j - 1 + m := ⟨N + 1 - 2 ^ j, by omega⟩
  have hmle : m ≤ 2 ^ j := by omega
  have hend := abs_defect_stage_end_le_of_stage C hC g L K hK δ hδ hstage j (by omega)
  have hstage' := defect_stage_eq C hC g L (j + 1) m (by omega) (by simpa using hmle)
  have hsum := hstage (j + 1) (by omega) m (by simpa using hmle)
  simp only [Nat.add_sub_cancel] at hstage' hsum
  rw [← hm] at hstage'
  have htri : |defect C g L N| ≤ |defect C g L (2 ^ j - 1)| +
      |defect C g L N - defect C g L (2 ^ j - 1)| := by
    have := abs_add_le (defect C g L (2 ^ j - 1)) (defect C g L N - defect C g L (2 ^ j - 1))
    simpa using this
  rw [hstage'] at htri
  have hpR : (2 : ℝ) ^ j ≤ (N : ℝ) + 1 := by exact_mod_cast hlo
  have e5 : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
  rw [hj]
  push_cast at hsum ⊢
  rw [e5] at hsum hend
  have hY : (0 : ℝ) ≤ δ * (C * ((j : ℝ) + 1)) := by positivity
  have hYj : (0 : ℝ) ≤ δ * C * 2 ^ j := by positivity
  have h6 : δ * ((C : ℝ) * j) * 2 ^ j ≤ δ * (C * ((j : ℝ) + 1)) * 2 ^ j := by
    nlinarith
  have h7 : δ * (C * ((j : ℝ) + 1)) * 2 ^ j ≤ δ * (C * ((j : ℝ) + 1)) * ((N : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hpR hY
  have e8 : 2 * δ * ((C : ℝ) * ((j : ℝ) + 1)) * ((N : ℝ) + 1) =
      2 * (δ * (C * ((j : ℝ) + 1)) * ((N : ℝ) + 1)) := by ring
  rw [e8]
  linarith

/-- The defect at the end of stage `k`, summed from stage `K`. -/
theorem abs_defect_stage_end_le (C : ℕ) (hC : 1 ≤ C) (g : ℕ → Bool) (L K : ℕ) (hK : 1 ≤ K)
    (δ : ℝ) (hδ : 0 < δ)
    (hmix : ∀ k, K ≤ k → ∀ m, m ≤ 2 ^ (k - 1) → ∀ t, k ≤ t → t + L ≤ C * k →
      |stageError g L k t m| ≤ δ * 2 ^ (k - 1))
    (k : ℕ) (hk : K ≤ k + 1) :
    |defect C g L (2 ^ k - 1)| ≤
      |defect C g L (2 ^ (K - 1) - 1)| + 2 ^ (k + 1) + δ * (C * k) * 2 ^ k :=
  abs_defect_stage_end_le_of_stage C hC g L K hK δ hδ
    (fun k hk m hm => abs_stage_sum_le C hC g L k m δ hδ (hmix k hk m hm)) k hk

/-- The defect at any word end at or beyond stage `K`. -/
theorem abs_defect_le (C : ℕ) (hC : 1 ≤ C) (g : ℕ → Bool) (L K : ℕ) (hK : 1 ≤ K)
    (δ : ℝ) (hδ : 0 < δ)
    (hmix : ∀ k, K ≤ k → ∀ m, m ≤ 2 ^ (k - 1) → ∀ t, k ≤ t → t + L ≤ C * k →
      |stageError g L k t m| ≤ δ * 2 ^ (k - 1))
    (N : ℕ) (hN : K ≤ Nat.size (N + 1)) :
    |defect C g L N| ≤
      |defect C g L (2 ^ (K - 1) - 1)| + 4 * ((N : ℝ) + 1) +
        2 * δ * (C * Nat.size (N + 1)) * ((N : ℝ) + 1) :=
  abs_defect_le_of_stage C hC g L K hK δ hδ
    (fun k hk m hm => abs_stage_sum_le C hC g L k m δ hδ (hmix k hk m hm)) N hN

/-- The `N + 1 − 2^B` integers `n ∈ [2^B, N]` each carry at least `B + 1` bits. -/
private theorem mul_succ_sub_le_cum (C : ℕ) (hC : 1 ≤ C) (B N : ℕ) :
    C * (B + 1) * (N + 1 - 2 ^ B) ≤ cum (champLen C) N := by
  have hpos : 0 < 2 ^ B := by positivity
  induction N with
  | zero =>
    have : 0 + 1 - 2 ^ B = 0 := by omega
    simp [this]
  | succ N ih =>
    rcases Nat.lt_or_ge (N + 1) (2 ^ B) with h | h
    · have : N + 1 + 1 - 2 ^ B = 0 := by omega
      simp [this]
    · have hs : B < Nat.size (N + 1) := Nat.lt_size.mpr h
      have hlen : C * (B + 1) ≤ champLen C N := by
        rw [champLen, max_eq_left hC]; exact Nat.mul_le_mul_left _ hs
      rw [show N + 1 + 1 - 2 ^ B = (N + 1 - 2 ^ B) + 1 by omega, mul_add, mul_one, cum_succ]
      omega

/-- The word ends carry the bit length: the upper half of `[1, N]` has `size ≥ k − 1`. -/
theorem mul_size_le_two_cum (C : ℕ) (hC : 1 ≤ C) (N : ℕ) :
    C * (Nat.size (N + 1) - 1) * (N + 1) ≤ 2 * cum (champLen C) N := by
  rcases Nat.lt_or_ge (Nat.size (N + 1)) 2 with hs | hs
  · have : Nat.size (N + 1) - 1 = 0 := by omega
    simp [this]
  · obtain ⟨B, hB⟩ : ∃ B, Nat.size (N + 1) = B + 2 := ⟨Nat.size (N + 1) - 2, by omega⟩
    have hlo : 2 ^ (B + 1) ≤ N + 1 := Nat.lt_size.mp (by omega)
    have hcount := mul_succ_sub_le_cum C hC B N
    rw [hB, show B + 2 - 1 = B + 1 by omega]
    have hdbl : 2 ^ (B + 1) = 2 * 2 ^ B := by ring
    have hle : N + 1 ≤ 2 * (N + 1 - 2 ^ B) := by omega
    calc C * (B + 1) * (N + 1) ≤ C * (B + 1) * (2 * (N + 1 - 2 ^ B)) :=
          Nat.mul_le_mul_left _ hle
      _ = 2 * (C * (B + 1) * (N + 1 - 2 ^ B)) := by ring
      _ ≤ 2 * cum (champLen C) N := Nat.mul_le_mul_left _ hcount

/-- `ShortIntervalMixing`, read as `stageError`. -/
theorem stageError_le_of_mixing (C : ℕ) (h : ShortIntervalMixing C) (g : ℕ → Bool) (L : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ k, K ≤ k → ∀ m, m ≤ 2 ^ (k - 1) → ∀ t, k ≤ t → t + L ≤ C * k →
      |stageError g L k t m| ≤ δ * 2 ^ (k - 1) := by
  obtain ⟨K₀, hK₀⟩ := h L (fun s => g s) δ hδ
  refine ⟨max K₀ 1, le_max_right _ _, fun k hk m hm t ht htL => ?_⟩
  have := hK₀ k (le_trans (le_max_left _ _) hk) m hm t ht htL
  have hf : (Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m)).filter (WindowMatch g L t) =
      (Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m)).filter
        fun n => ∀ s : Fin L, accWord n (t + s) = g s := by
    apply Finset.filter_congr
    intro n _
    simp [WindowMatch, Fin.forall_iff]
  rw [stageError, hf]
  exact this

/-- A bound on the signed sum over the fitting offsets of each stage segment makes `𝒞_C` normal. -/
theorem normal_of_stage_bound (C : ℕ) (hC : 1 ≤ C)
    (hs : ∀ (u : List Bool) (δ : ℝ), 0 < δ → ∃ K : ℕ, 1 ≤ K ∧ ∀ k, K ≤ k → ∀ m, m ≤ 2 ^ (k - 1) →
      |∑ t ∈ (Finset.range (C * k)).filter (fun t => t + u.length ≤ C * k),
          stageError (fun s => u.getD s false) u.length k t m| ≤
        2 ^ k + δ * (C * k) * 2 ^ (k - 1)) :
    Normal (collatzChampernowne C) := by
  intro u
  rcases Nat.eq_zero_or_pos u.length with h0 | hu
  · have hu0 : u = [] := List.length_eq_zero_iff.mp h0
    subst hu0
    refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_ |>.trans (by simp)
    filter_upwards [eventually_gt_atTop 0] with k hk
    rw [occ_nil, div_self (by exact_mod_cast hk.ne')]
  rw [Metric.tendsto_nhds]
  intro ε hε
  set g : ℕ → Bool := fun s => u.getD s false with hg
  set L := u.length with hL
  obtain ⟨K, hK1, hstage⟩ := hs u (ε / 16) (by positivity)
  set E₀ := |defect C g L (2 ^ (K - 1) - 1)| with hE₀
  have hE0 : 0 ≤ E₀ := abs_nonneg _
  set A : ℝ := E₀ + 2 * L + 4 + 2 * C with hA
  have hApos : 0 < A := by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ C := Nat.cast_nonneg _
    rw [hA]; linarith
  set W := wordIndex (champLen C) (one_le_champLen C) with hW
  have hWtend : Tendsto W atTop atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [eventually_ge_atTop (cum (champLen C) b)] with P hP
    by_contra hlt
    have h2 : P < cum (champLen C) (W P + 1) := (cum_le_wordIndex C P).2
    have := cum_mono (champLen C) (show W P + 1 ≤ b by omega)
    omega
  have hsmall : ∀ᶠ N : ℕ in atTop, ((N : ℝ) + 1) / (cum (champLen C) N : ℝ) < ε / (2 * A) := by
    have := tendsto_succ_div_cum C
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hWtend.eventually hsmall, hWtend.eventually_ge_atTop (2 ^ K + 1)] with P hsm hPK
  set N := W P with hN
  obtain ⟨h₁, h₂⟩ : cum (champLen C) N ≤ P ∧ P < cum (champLen C) (N + 1) := cum_le_wordIndex C P
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hPK
  have hcpos : 0 < cum (champLen C) N := by
    have := le_cum (champLen C) (one_le_champLen C) N
    omega
  have hcR : (0 : ℝ) < cum (champLen C) N := by exact_mod_cast hcpos
  have hPR : (cum (champLen C) N : ℝ) ≤ P := by exact_mod_cast h₁
  have hPpos : (0 : ℝ) < P := lt_of_lt_of_le hcR hPR
  set k := Nat.size (N + 1) with hk
  have hkK : K ≤ k := (Nat.lt_size.mpr (by omega : 2 ^ K ≤ N + 1)).le
  have hk2 : 2 ≤ k := by
    have : 1 < k := Nat.lt_size.mpr (by simpa using (by omega : 2 ≤ N + 1))
    omega
  have hkN : k ≤ N + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have hlen : champLen C N = C * k := by rw [champLen, max_eq_left hC]
  have hd := abs_defect_le_of_stage C hC g L K hK1 (ε / 16) (by positivity) hstage N hkK
  rw [← hk, ← hE₀] at hd
  obtain ⟨hol, hou⟩ := occ_cum_le C u N
  have hmain := abs_main_sub_cum_le C L N
  have hpre := abs_occ_sub_le_of_cum C u N P h₁ h₂
  rw [← hL] at hpre
  have hsize := mul_size_le_two_cum C hC N
  rw [← hk] at hsize
  -- the real-number inputs
  have holR : (interior C g L N : ℝ) ≤ occ (collatzChampernowne C) u (cum (champLen C) N) := by
    exact_mod_cast hol
  have houR : (occ (collatzChampernowne C) u (cum (champLen C) N) : ℝ) ≤
      interior C g L N + L * N := by exact_mod_cast hou
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hLR : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hCR : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hLN : (0 : ℝ) ≤ L * N := by positivity
  have hLN' : (L : ℝ) * N ≤ L * ((N : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hLR
  have hcumb : |(occ (collatzChampernowne C) u (cum (champLen C) N) : ℝ) -
      (cum (champLen C) N : ℝ) / 2 ^ L| ≤ L * N + |defect C g L N| + L * N := by
    have hdl := le_abs_self (defect C g L N)
    have hdn := neg_abs_le (defect C g L N)
    have hD : defect C g L N = (interior C g L N : ℝ) - (windowCount C L N : ℝ) / 2 ^ L := rfl
    rw [abs_le] at hmain ⊢
    constructor <;> linarith [hmain.1, hmain.2]
  have hlenR : (champLen C N : ℝ) ≤ C * ((N : ℝ) + 1) := by
    have : champLen C N ≤ C * (N + 1) := by rw [hlen]; exact Nat.mul_le_mul_left _ hkN
    exact_mod_cast this
  have hkk : C * k * (N + 1) ≤ 4 * cum (champLen C) N := by
    have h3 : C * k * (N + 1) ≤ 2 * (C * (k - 1) * (N + 1)) := by
      have : k ≤ 2 * (k - 1) := by omega
      calc C * k * (N + 1) ≤ C * (2 * (k - 1)) * (N + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
        _ = _ := by ring
    omega
  have hkkR : (C : ℝ) * k * ((N : ℝ) + 1) ≤ 4 * cum (champLen C) N := by exact_mod_cast hkk
  have hAb : A * ((N : ℝ) + 1) < ε / 2 * cum (champLen C) N := by
    rw [div_lt_div_iff₀ hcR (by positivity)] at hsm
    linarith
  have hE1 : E₀ ≤ E₀ * ((N : ℝ) + 1) := by
    have := mul_nonneg hE0 hNR
    linarith
  have htail : 2 * (ε / 16) * ((C : ℝ) * k) * ((N : ℝ) + 1) ≤ ε / 2 * cum (champLen C) N := by
    have : 2 * (ε / 16) * ((C : ℝ) * k) * ((N : ℝ) + 1) =
        ε / 8 * ((C : ℝ) * k * ((N : ℝ) + 1)) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hkkR (by positivity : (0 : ℝ) ≤ ε / 8)
    linarith
  have htotal : |(occ (collatzChampernowne C) u P : ℝ) - (P : ℝ) / 2 ^ L| < ε * P := by
    have hexp : A * ((N : ℝ) + 1) =
        E₀ * ((N : ℝ) + 1) + 2 * (L * ((N : ℝ) + 1)) + 4 * ((N : ℝ) + 1) +
          2 * (C * ((N : ℝ) + 1)) := by rw [hA]; ring
    have hεc : ε * cum (champLen C) N ≤ ε * P := mul_le_mul_of_nonneg_left hPR hε.le
    linarith
  have heq : (occ (collatzChampernowne C) u P : ℝ) / P - (1 / 2 : ℝ) ^ L =
      ((occ (collatzChampernowne C) u P : ℝ) - (P : ℝ) / 2 ^ L) / P := by
    rw [one_div, inv_pow]; field_simp
  rw [Real.dist_eq, heq, abs_div, abs_of_pos hPpos, div_lt_iff₀ hPpos]
  exact htotal

/-- **Short-interval mixing makes `𝒞_C` normal.**  The hypothesis is used uniformly in `m`, since
a prefix may be cut anywhere inside a stage; without that uniformity the block frequencies could
oscillate within a stage. -/
theorem normal_of_shortIntervalMixing (C : ℕ) (hC : 1 ≤ C) (h : ShortIntervalMixing C) :
    Normal (collatzChampernowne C) := by
  refine normal_of_stage_bound C hC fun u δ hδ => ?_
  obtain ⟨K, hK, hmix⟩ := stageError_le_of_mixing C h (fun s => u.getD s false) u.length δ hδ
  exact ⟨K, hK, fun k hk m hm => abs_stage_sum_le C hC _ _ k m δ hδ (hmix k hk m hm)⟩

theorem champernowneNormalBelowThreshold_of_shortIntervalMixing
    (h : ∀ C, 1 ≤ C → C ≤ 4 → ShortIntervalMixing C) : ChampernowneNormalBelowThreshold :=
  fun C h1 h4 => normal_of_shortIntervalMixing C h1 (h C h1 h4)

end CollatzMoonshot.Conjugacy
