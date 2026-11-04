/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.C1
import CollatzMoonshot.Conjugacy.ResidueIndicator

/-!
# Beyond-Terras words of every fixed length are uniform (the `K`-letter C1)

C1 (`biasDecays`) says the `j`-th parity letter of the orbit of a uniform `j`-bit start is
asymptotically balanced.  The first `K` letters past the Terras horizon — the parities of
`T^j r, T^{j+1} r, …, T^{j+K−1} r` — are determined by `T^j r mod 2^K` (Terras: the first `K`
parities of the orbit of `m` are a bijective function of `m mod 2^K`).  So the natural
strengthening is: `T^j r mod 2^K` is asymptotically uniform over `r < 2^j`, for every fixed `K`.

## Mechanism (paper, 2026-11-03, Ren)

Follow `biasDecays_of_sliceCharDecay` (SliceFourier.lean) verbatim, replacing least-residue parity
`(−1)^y` by the centred indicator `g_c(y) = 1[y ≡ c (mod 2^K)] − 2^{−K}` on `[0, 3^a)`:

* `T^j r < 3^a` on the slice `levelSet j a` (`tstep_iterate_lt_three_pow`), so the slice count of
  `{r : T^j r ≡ c}` is `Σ_y levelMass(y) · 1[y ≡ c]`, read through `y mod 3^a`.
* Fourier on `ℤ/3^a` (odd modulus, `2^K` invertible):
  `ĝ_c(ξ) = 3^{−a} e(−ξc/3^a) Σ_{t < ⌈(3^a−c)/2^K⌉} e(−ξ 2^K t/3^a)`, a geometric sum, so
  `|ĝ_c(ξ)| ≤ 3^{−a} min(3^a/2^K + 1, 1/|sin(π ξ 2^K / 3^a)|)`.  As `ξ` runs over `ℤ/3^a`, so does
  `ξ 2^K`; hence `Σ_ξ |ĝ_c(ξ)| = O(a)`, uniformly in `K` and `c` (compare `sum_norm_gHatZ_le`).
* The `v₃(ξ) = k` layering (`sum_norm_gHatZ_dvd_le`, `sliceChar_eq_subsliceSum`) and the binomial
  tails (`abs_bias_le_of_levelSign`, `outOddSet`) are unchanged: they never used the specific `g`.
* So the centred slice count is `≤ ε · #slice` eventually, uniformly on the central window, and
  the assembly over `a` gives `beyondCount j K c = 2^{j−K} + o(2^j)`.

The cleanest route is to generalise the pipeline to an arbitrary `g : ℕ → ℂ` supported on `[0, 3^a)`
with a Fourier-weight bound `Σ_ξ ‖ĝ(ξ)‖ ≤ C · (a + 1)`, then instantiate twice: `(−1)^y` recovers
C1, the centred indicator gives this file.

## Status

Proved (2026-11-04).  `beyondWordsUniform_of_sliceCharDecay` assembles the generic pipeline
(`SliceFourierGeneral.lean`: `eventually_norm_levelSum_le`, `norm_sum_range_le_of_levelSum`) with
the layered weight of the centred indicator (`ResidueIndicator.lean`: `layeredWeight_resInd`);
`beyondWordsUniform` is unconditional through the Sec7P node.  `biasDecays_of_beyondWordsUniform`
is the consistency check (`K = 1`, `c = 0`).  The statements stay frozen.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- The number of `j`-bit starts whose `j`-th Terras iterate is `≡ c (mod 2^K)`: the starts whose
beyond-Terras word of length `K` is the word encoded by `c`. -/
def beyondCount (j K c : ℕ) : ℕ :=
  ((Finset.range (2 ^ j)).filter (fun r => tstep^[j] r % 2 ^ K = c)).card

/-- Teeth: `K = 1`, `c = 0` counts even `j`-th iterates, `(2^j + bias j)/2`. -/
example : beyondCount 3 1 0 = 7 := by decide
example : beyondCount 4 1 0 = 11 := by decide
example : beyondCount 5 1 0 = 23 := by decide
/-- Teeth: the residues mod `4` of `T^4 r`, `r < 16`, partition the `16` starts. -/
example : beyondCount 4 2 0 + beyondCount 4 2 1 + beyondCount 4 2 2 + beyondCount 4 2 3 = 16 := by
  decide

/-- **Beyond-Terras words are uniform.**  For every fixed `K` and every residue `c < 2^K`, the
proportion of `j`-bit starts with `T^j r ≡ c (mod 2^K)` tends to `2^{−K}`.  `K = 1` is C1. -/
def BeyondWordsUniform : Prop :=
  ∀ K c : ℕ, c < 2 ^ K →
    Tendsto (fun j : ℕ => (beyondCount j K c : ℝ) / 2 ^ j) atTop (𝓝 (1 / 2 ^ K))

/-- The centred indicator is bounded by `1`. -/
theorem norm_resInd_le_one (K c y : ℕ) : ‖resInd K c y‖ ≤ 1 := by
  have hq : (0 : ℝ) < ((2 : ℝ) ^ K)⁻¹ := by positivity
  have hq1 : ((2 : ℝ) ^ K)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have heq : resInd K c y =
      (((if y % 2 ^ K = c then 1 else 0) - ((2 : ℝ) ^ K)⁻¹ : ℝ) : ℂ) := by
    unfold resInd
    push_cast
    split_ifs <;> simp
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
  split_ifs <;> constructor <;> linarith

/-- The full sum of the centred indicator over `j`-bit starts is the centred count
`beyondCount j K c − 2^j/2^K`. -/
theorem sum_resInd_eq (j K c : ℕ) :
    ∑ r ∈ Finset.range (2 ^ j), resInd K c (tstep^[j] r) =
      (beyondCount j K c : ℂ) - 2 ^ j * ((2 : ℂ) ^ K)⁻¹ := by
  unfold resInd beyondCount
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  push_cast
  ring

/-- **Frozen target (2026-11-03).**  Slice character decay gives uniformity of every fixed-length
beyond-Terras word, by the Fourier expansion of the centred indicator `1[y ≡ c (2^K)] − 2^{−K}` on
`ℤ/3^a` (weight `O(a)` uniformly in `K`, `c`), exactly as `biasDecays_of_sliceCharDecay` handles
`(−1)^y`.  Confidence 85%. -/
theorem beyondWordsUniform_of_sliceCharDecay (h : SliceCharDecay) : BeyondWordsUniform := by
  intro K c hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hslices := eventually_norm_levelSum_le h 1 zero_le_one (ε / 2) (by positivity)
  rw [Filter.eventually_atTop] at hslices
  obtain ⟨J, hJ⟩ := hslices
  obtain ⟨M, hM⟩ := exists_nat_gt (200 / ε)
  refine ⟨max J (M + 1), fun j hj => ?_⟩
  have hjJ : J ≤ j := le_trans (le_max_left _ _) hj
  have hMj : M + 1 ≤ j := le_trans (le_max_right _ _) hj
  have hjpos : 0 < j := by omega
  have hjreal : 200 / ε < (j : ℝ) := by
    exact hM.trans_le (by exact_mod_cast (show M ≤ j by omega))
  have htailSmall : 100 / (j : ℝ) < ε / 2 := by
    have hcross : (200 : ℝ) < ε * j := by
      rwa [div_lt_iff₀' hε] at hjreal
    have hjrealpos : (0 : ℝ) < j := by exact_mod_cast hjpos
    rw [div_lt_iff₀ hjrealpos]
    nlinarith
  have hsum := norm_sum_range_le_of_levelSum j (resInd K c) (norm_resInd_le_one K c)
    (show 0 ≤ ε / 2 by positivity)
    (fun a ha1 ha2 => hJ j hjJ a ha1 ha2 (resInd K c) (layeredWeight_resInd hc a))
  rw [sum_resInd_eq] at hsum
  have hnormeq : ‖(beyondCount j K c : ℂ) - 2 ^ j * ((2 : ℂ) ^ K)⁻¹‖ =
      |(beyondCount j K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹| := by
    have hr := Complex.norm_real ((beyondCount j K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹)
    push_cast at hr
    rw [hr, Real.norm_eq_abs]
  rw [hnormeq] at hsum
  have hpowpos : (0 : ℝ) < 2 ^ j := by positivity
  have htail := outOddSet_ratio_le j hjpos
  have hdist : dist ((beyondCount j K c : ℝ) / 2 ^ j) (1 / 2 ^ K) =
      |(beyondCount j K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹| / 2 ^ j := by
    rw [Real.dist_eq, ← abs_of_pos hpowpos, ← abs_div, abs_of_pos hpowpos]
    congr 1
    field_simp
  rw [hdist]
  have hnorm :
      |(beyondCount j K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹| / 2 ^ j ≤
        ε / 2 + ((outOddSet j).card : ℝ) / 2 ^ j := by
    apply (div_le_iff₀ hpowpos).2
    calc
      _ ≤ (ε / 2) * 2 ^ j + ((outOddSet j).card : ℝ) := hsum
      _ = (ε / 2 + ((outOddSet j).card : ℝ) / 2 ^ j) * 2 ^ j := by
        field_simp
  linarith

/-- Unconditional, through the Sec7P node. -/
theorem beyondWordsUniform : BeyondWordsUniform :=
  beyondWordsUniform_of_sliceCharDecay (sliceCharDecay_of_pascalDampingDecay pascalDampingDecay)

/-- The bias is the excess of even over odd `j`-th iterates:
`bias j = 2 · beyondCount j 1 0 − 2^j`. -/
theorem bias_eq_two_mul_beyondCount (j : ℕ) :
    bias j = 2 * (beyondCount j 1 0 : ℤ) - 2 ^ j := by
  unfold bias beyondCount
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, pow_one]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range (2 ^ j))
    (fun r => tstep^[j] r % 2 = 0)
  rw [Finset.card_range] at h
  simp only [nsmul_eq_mul, mul_one, mul_neg]
  have h' : (((Finset.range (2 ^ j)).filter (fun r => tstep^[j] r % 2 = 0)).card : ℤ) +
      (((Finset.range (2 ^ j)).filter (fun r => ¬ tstep^[j] r % 2 = 0)).card : ℤ) = 2 ^ j := by
    exact_mod_cast h
  linarith

/-- Consistency: `K = 1`, `c = 0` is `BiasDecays`, since `bias j = 2 · beyondCount j 1 0 − 2^j`. -/
theorem biasDecays_of_beyondWordsUniform (h : BeyondWordsUniform) : BiasDecays := by
  have h1 := h 1 0 (by norm_num)
  have hlim : Tendsto (fun j : ℕ => 2 * ((beyondCount j 1 0 : ℝ) / 2 ^ j) - 1) atTop
      (𝓝 (2 * (1 / 2 ^ 1) - 1)) := (h1.const_mul 2).sub_const 1
  norm_num at hlim
  unfold BiasDecays
  refine hlim.congr' (Eventually.of_forall fun j => ?_)
  have hb := congrArg (fun z : ℤ => (z : ℝ)) (bias_eq_two_mul_beyondCount j)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_pow] at hb
  simp only [hb]
  field_simp

end CollatzMoonshot.Conjugacy
