/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.ChampernowneMixing
import CollatzMoonshot.Conjugacy.ChampernowneThreshold
import CollatzMoonshot.Conjugacy.ChampernowneDrift

/-!
# Normality of `𝒞_C` is exactly averaged mixing

`ShortIntervalMixing C` bounds each offset `t ∈ [k, C k)` separately.  Normality only sees the signed
sum over those offsets, of size `o(k 2^k)`, uniformly in the initial segment of the stage.  That sum
is `AveragedMixing C`, and it is equivalent to normality (`normal_iff_averagedMixing`).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- **The exact target for `1 < C < C*`.**  For every word `u` and `δ > 0`, for all large `k` and
every initial segment of stage `k`, the signed window errors summed over the offsets `t ≥ k` total at
most `δ k 2^(k-1)`. -/
def AveragedMixing (C : ℕ) : Prop :=
  ∀ (u : List Bool) (δ : ℝ), 0 < δ → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ m : ℕ, m ≤ 2 ^ (k - 1) →
    |∑ t ∈ (Finset.range (C * k)).filter (fun t => k ≤ t ∧ t + u.length ≤ C * k),
        stageError (fun s => u.getD s false) u.length k t m| ≤ δ * k * 2 ^ (k - 1)

/-- The fitting offsets split into those below `k` and the offsets of `AveragedMixing`. -/
theorem stage_sum_split (C : ℕ) (g : ℕ → Bool) (L k m : ℕ) :
    ∑ t ∈ (Finset.range (C * k)).filter (fun t => t + L ≤ C * k), stageError g L k t m =
      ∑ t ∈ ((Finset.range (C * k)).filter (fun t => t + L ≤ C * k)).filter (fun t => t < k),
          stageError g L k t m +
        ∑ t ∈ (Finset.range (C * k)).filter (fun t => k ≤ t ∧ t + L ≤ C * k),
          stageError g L k t m := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun t => t < k)]
  congr 2
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, not_lt]
  tauto

/-- The defect at a word end is the occurrence error there, up to `2 L N` boundary terms. -/
theorem abs_defect_sub_occ_le (C : ℕ) (u : List Bool) (N : ℕ) :
    |defect C (fun s => u.getD s false) u.length N -
        ((occ (collatzChampernowne C) u (cum (champLen C) N) : ℝ) -
          (cum (champLen C) N : ℝ) / 2 ^ u.length)| ≤ 2 * (u.length * N) := by
  obtain ⟨hol, hou⟩ := occ_cum_le C u N
  have hmain := abs_main_sub_cum_le C u.length N
  have holR : (interior C (fun s => u.getD s false) u.length N : ℝ) ≤
      occ (collatzChampernowne C) u (cum (champLen C) N) := by exact_mod_cast hol
  have houR : (occ (collatzChampernowne C) u (cum (champLen C) N) : ℝ) ≤
      interior C (fun s => u.getD s false) u.length N + u.length * N := by exact_mod_cast hou
  have hLN : (0 : ℝ) ≤ u.length * N := by positivity
  simp only [defect]
  rw [abs_le] at hmain ⊢
  constructor <;> linarith [hmain.1, hmain.2]

/-- Bounding each offset bounds the sum. -/
theorem averagedMixing_of_shortIntervalMixing (C : ℕ) (hC : 1 ≤ C) (h : ShortIntervalMixing C) :
    AveragedMixing C := by
  intro u δ hδ
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  obtain ⟨K, -, hmix⟩ := stageError_le_of_mixing C h (fun s => u.getD s false) u.length
    (δ / C) (by positivity)
  refine ⟨K, fun k hk m hm => (Finset.abs_sum_le_sum_abs _ _).trans ?_⟩
  have hb : ∀ t ∈ (Finset.range (C * k)).filter (fun t => k ≤ t ∧ t + u.length ≤ C * k),
      |stageError (fun s => u.getD s false) u.length k t m| ≤ δ / C * 2 ^ (k - 1) := by
    intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    exact hmix k hk m hm t ht'.1 ht'.2
  refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
  have hcard : ((Finset.range (C * k)).filter
      (fun t => k ≤ t ∧ t + u.length ≤ C * k)).card ≤ C * k :=
    (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  have hcR : (((Finset.range (C * k)).filter
      (fun t => k ≤ t ∧ t + u.length ≤ C * k)).card : ℝ) ≤ C * k := by exact_mod_cast hcard
  rw [nsmul_eq_mul]
  have hX : (0 : ℝ) ≤ δ / C * 2 ^ (k - 1) := by positivity
  calc _ ≤ ((C : ℝ) * k) * (δ / C * 2 ^ (k - 1)) := mul_le_mul_of_nonneg_right hcR hX
    _ = δ * k * 2 ^ (k - 1) := by field_simp

/-- Averaged mixing makes `𝒞_C` normal: the offsets below `k` cost `2^k` by Terras. -/
theorem normal_of_averagedMixing (C : ℕ) (hC : 1 ≤ C) (h : AveragedMixing C) :
    Normal (collatzChampernowne C) := by
  refine normal_of_stage_bound C hC fun u δ hδ => ?_
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  obtain ⟨K₀, hK₀⟩ := h u (C * δ) (by positivity)
  refine ⟨max K₀ 1, le_max_right _ _, fun k hk m hm => ?_⟩
  have hhigh := hK₀ k (le_trans (le_max_left _ _) hk) m hm
  have hlow := abs_stage_sum_low_le C (fun s => u.getD s false) u.length k m
  rw [stage_sum_split]
  refine (abs_add_le _ _).trans (add_le_add hlow (hhigh.trans_eq ?_))
  ring

/-- Normality gives averaged mixing: a stage segment is a difference of two word-end prefixes. -/
theorem averagedMixing_of_normal (C : ℕ) (hC : 1 ≤ C) (h : Normal (collatzChampernowne C)) :
    AveragedMixing C := by
  intro u δ hδ
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  set g : ℕ → Bool := fun s => u.getD s false with hg
  set L := u.length with hL
  set ε : ℝ := δ / (16 * C) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨P₀, hP₀⟩ := Metric.tendsto_atTop.mp (h u) ε hεpos
  have hocc : ∀ P : ℕ, max P₀ 1 ≤ P →
      |(occ (collatzChampernowne C) u P : ℝ) - (P : ℝ) / 2 ^ L| ≤ ε * P := by
    intro P hP
    have hPpos : (0 : ℝ) < P := by
      have : 1 ≤ P := le_trans (le_max_right _ _) hP
      exact_mod_cast this
    have hd := hP₀ P (le_trans (le_max_left _ _) hP)
    have heq : (occ (collatzChampernowne C) u P : ℝ) / P - (1 / 2 : ℝ) ^ L =
        ((occ (collatzChampernowne C) u P : ℝ) - (P : ℝ) / 2 ^ L) / P := by
      rw [one_div, inv_pow]; field_simp
    rw [Real.dist_eq, heq, abs_div, abs_of_pos hPpos, div_lt_iff₀ hPpos] at hd
    exact hd.le
  refine ⟨max (max P₀ 1 + 1) ⌈4 * (8 * (L : ℝ) + 2) / δ⌉₊, fun k hk m hm => ?_⟩
  have hkP : max P₀ 1 + 1 ≤ k := le_trans (le_max_left _ _) hk
  have hk1 : 1 ≤ k := by omega
  have hkδ : 4 * (8 * (L : ℝ) + 2) ≤ δ * k := by
    have h1 : 4 * (8 * (L : ℝ) + 2) / δ ≤ k :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hk)
    rw [div_le_iff₀ hδ] at h1
    linarith
  have hTpos : 0 < 2 ^ (k - 1) := by positivity
  have hdbl : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hlt : k - 1 < 2 ^ (k - 1) := Nat.lt_two_pow_self
  -- the bound at the two word ends
  have hend : ∀ N : ℕ, 2 ^ (k - 1) - 1 ≤ N → N ≤ 2 ^ k - 1 →
      |defect C g L N| ≤ δ / 8 * k * 2 ^ (k - 1) + 4 * (L * 2 ^ (k - 1)) := by
    intro N hN0 hN1
    have hlo : max P₀ 1 ≤ cum (champLen C) N :=
      le_trans (by omega) (le_cum (champLen C) (one_le_champLen C) N)
    have hup : cum (champLen C) N ≤ C * k * 2 ^ k :=
      (cum_mono (champLen C) hN1).trans (cum_stage_end_le C hC k)
    have hD := hocc _ hlo
    have hsub := abs_defect_sub_occ_le C u N
    have hupR : (cum (champLen C) N : ℝ) ≤ C * k * (2 * 2 ^ (k - 1)) := by
      have : (cum (champLen C) N : ℝ) ≤ ((C * k * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hup
      rw [hdbl] at this
      push_cast at this
      exact this
    have hεup : ε * cum (champLen C) N ≤ δ / 8 * k * 2 ^ (k - 1) := by
      calc ε * cum (champLen C) N ≤ ε * (C * k * (2 * 2 ^ (k - 1))) :=
            mul_le_mul_of_nonneg_left hupR hεpos.le
        _ = δ / 8 * k * 2 ^ (k - 1) := by rw [hε]; field_simp; ring
    have hNR : (N : ℝ) ≤ 2 * 2 ^ (k - 1) := by
      have : N ≤ 2 * 2 ^ (k - 1) := by omega
      exact_mod_cast this
    have hLN : (L : ℝ) * N ≤ L * (2 * 2 ^ (k - 1)) :=
      mul_le_mul_of_nonneg_left hNR (Nat.cast_nonneg _)
    have htri : |defect C g L N| ≤
        |defect C g L N - ((occ (collatzChampernowne C) u (cum (champLen C) N) : ℝ) -
            (cum (champLen C) N : ℝ) / 2 ^ L)| +
          |(occ (collatzChampernowne C) u (cum (champLen C) N) : ℝ) -
            (cum (champLen C) N : ℝ) / 2 ^ L| := by
      have := abs_add_le (defect C g L N - ((occ (collatzChampernowne C) u (cum (champLen C) N) : ℝ) -
            (cum (champLen C) N : ℝ) / 2 ^ L))
          ((occ (collatzChampernowne C) u (cum (champLen C) N) : ℝ) -
            (cum (champLen C) N : ℝ) / 2 ^ L)
      simpa using this
    have e : (L : ℝ) * (2 * 2 ^ (k - 1)) = 2 * (L * 2 ^ (k - 1)) := by ring
    linarith
  have hd₀ := hend (2 ^ (k - 1) - 1) le_rfl (by omega)
  have hd₁ := hend (2 ^ (k - 1) - 1 + m) (by omega) (by omega)
  have hstage := defect_stage_eq C hC g L k m hk1 hm
  rw [stage_sum_split] at hstage
  have hlow := abs_stage_sum_low_le C g L k m
  have hTR : (0 : ℝ) < 2 ^ (k - 1) := by positivity
  have hlowR : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by exact_mod_cast hdbl
  rw [hlowR] at hlow
  have hfin : (8 * (L : ℝ) + 2) * 2 ^ (k - 1) ≤ δ / 4 * k * 2 ^ (k - 1) := by
    refine mul_le_mul_of_nonneg_right ?_ hTR.le
    linarith
  rw [abs_le] at hd₀ hd₁ hlow ⊢
  constructor <;> nlinarith [hd₀.1, hd₀.2, hd₁.1, hd₁.2, hlow.1, hlow.2, hfin]

/-- **Normality of `𝒞_C` is exactly averaged mixing.** -/
theorem normal_iff_averagedMixing (C : ℕ) (hC : 1 ≤ C) :
    Normal (collatzChampernowne C) ↔ AveragedMixing C :=
  ⟨averagedMixing_of_normal C hC, normal_of_averagedMixing C hC⟩

/-- Above the threshold averaged mixing fails, with no hypothesis. -/
theorem not_averagedMixing_of_five_le (C : ℕ) (hC : 5 ≤ C) : ¬ AveragedMixing C :=
  fun h => not_normal_of_five_le C hC (normal_of_averagedMixing C (by omega) h)

/-- Above the threshold short-interval mixing fails, with no hypothesis. -/
theorem not_shortIntervalMixing_of_five_le (C : ℕ) (hC : 5 ≤ C) : ¬ ShortIntervalMixing C :=
  fun h => not_normal_of_five_le C hC (normal_of_shortIntervalMixing C (by omega) h)

end CollatzMoonshot.Conjugacy
