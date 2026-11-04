/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.C1

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

`beyondWordsUniform_of_sliceCharDecay` is the frozen target (sorry, confidence 85%);
`biasDecays_of_beyondWordsUniform` is the consistency check (`K = 1`, `c = 0`).  Do not restate
or weaken either; split into named lemmas instead.
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

/-- **Frozen target (2026-11-03).**  Slice character decay gives uniformity of every fixed-length
beyond-Terras word, by the Fourier expansion of the centred indicator `1[y ≡ c (2^K)] − 2^{−K}` on
`ℤ/3^a` (weight `O(a)` uniformly in `K`, `c`), exactly as `biasDecays_of_sliceCharDecay` handles
`(−1)^y`.  Confidence 85%. -/
theorem beyondWordsUniform_of_sliceCharDecay (h : SliceCharDecay) : BeyondWordsUniform := by
  sorry

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
