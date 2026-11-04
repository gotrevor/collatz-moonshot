/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitHeightLaw
import CollatzMoonshot.Conjugacy.OrbitStageLawPull
import CollatzMoonshot.Conjugacy.OrbitStageLawRate

/-!
# The orbit word law over one stage, and normality for `C ≤ 4`

`StageWordLaw C` for `C ≤ 4` needs no mixing.  The exceptional sets are Terras events, of density
`≪ X^(−D)`, and a set of that density pulls back along `T^(size m)` to a set of the same kind
(Inselmann 2024, arXiv:2402.03276, Lemma 2.16): `M = T^k m = 3^a m / 2^k + offset` pins `m` to an
interval once `M` and `a` are known, so the argument uses the size of `M`, not its residue.  Windows of
`size M_j` letters of `M_j` then cover `(1 + θ + θ² + …) size m` letters, `θ = log₂ √3`, and nine of them
cover `4.225 size m`.  With `not_normal_of_five_le` this gives `normal_iff_le_four`.

`RESEARCH-2026-11-04-affine-mixing.md` §7 is the argument.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-! ## The four pieces

`stageWordLaw_of_le_four` is assembled from four leaves.

* **P1** (`expSparse_not_goodZero`): the one-window good event fails on an exponentially sparse set.
  Exponential moments over `|u|`-spaced blocks, which are independent by Terras.
* **P2** (`expSparse_preimage_stageMap`): pulling back along `stageMap` keeps a set exponentially
  sparse (Inselmann 2024, Lemma 2.16).  Given `a = oddCount n k` and `M = stageMap n`,
  `2^k M − 3^a n ∈ [0, k 2^(k + ℓ₀)]` pins `n` to an interval of length `k 2^(k + ℓ₀) / 3^a`, and
  `M < 3^a (1 + k 2^ℓ₀)`.
* **P3/P4** (`not_badStart_of_chain`): if `stageMap^[j] m` is good for `j < J`, the windows of
  `size (stageMap^[j] m)` letters cover `(1 + θ + … + θ^(J−1) − O(1/k)) size m ≥ 4 size m` letters,
  `θ = 39/50 < log₂ √3`, each with deviation `≤ δ size m / (2J)`.
* **Density** (`tendsto_stage_of_expSparse`).
-/

/-- **P1.**  The one-window good event fails on an exponentially sparse set. -/
theorem expSparse_not_goodZero (u : List Bool) {η γ : ℝ} (hη : 0 < η) (hγ : 0 < γ) :
    ExpSparse {n | ¬ GoodZero u η γ n} := by
  sorry

/-- **P2, the pullback.**  Pulling back along `stageMap` keeps a set exponentially sparse. -/
theorem expSparse_preimage_stageMap {B : Set ℕ} (h : ExpSparse B) :
    ExpSparse (stageMap ⁻¹' B) := by
  sorry

/-- Finite unions of exponentially sparse sets are exponentially sparse. -/
theorem expSparse_biUnion_range (J : ℕ) (B : ℕ → Set ℕ) (h : ∀ j < J, ExpSparse (B j)) :
    ExpSparse (⋃ j ∈ Finset.range J, B j) :=
  expSparse_biUnion_range' J B h

/-- **P3/P4, the windows.**  For `C ≤ 4`, a start whose first `J` windows are good is not bad. -/
theorem not_badStart_of_chain (C : ℕ) (hC4 : C ≤ 4) (u : List Bool) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (η γ : ℝ) (J k₀ : ℕ), 0 < η ∧ 0 < γ ∧ ∀ m : ℕ, 1 ≤ m → k₀ ≤ Nat.size m →
      (∀ j < J, GoodZero u η γ (stageMap^[j] m)) → ¬ BadStart C u δ m := by
  sorry

open Classical in
/-- **Density.**  A property that eventually forces membership in an exponentially sparse set has
stage density `0`. -/
theorem tendsto_stage_of_expSparse {B : Set ℕ} (hB : ExpSparse B) (P : ℕ → Prop) (k₀ : ℕ)
    (hP : ∀ k ≥ k₀, ∀ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k), P n → n ∈ B) :
    Tendsto (fun k : ℕ => (((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter P).card : ℝ) / 2 ^ (k - 1))
      atTop (𝓝 0) :=
  tendsto_stage_of_expSparse' hB P k₀ hP

/-- **The orbit word law over one stage, for `C ≤ 4`.**  Believed, 88%. -/
theorem stageWordLaw_of_le_four (C : ℕ) (hC : 1 ≤ C) (hC4 : C ≤ 4) : StageWordLaw C := by
  classical
  intro u δ hδ
  obtain ⟨η, γ, J, k₀, hη, hγ, hchain⟩ := not_badStart_of_chain C hC4 u hδ
  have hB : ExpSparse (⋃ j ∈ Finset.range J, (stageMap^[j]) ⁻¹' {n | ¬ GoodZero u η γ n}) := by
    refine expSparse_biUnion_range J _ fun j _ => ?_
    induction j with
    | zero => simpa using expSparse_not_goodZero u hη hγ
    | succ j ih =>
      rw [Function.iterate_succ, Set.preimage_comp]
      exact expSparse_preimage_stageMap (ih (by omega))
  refine tendsto_stage_of_expSparse hB _ (max k₀ 1) fun k hk n hn hbad => ?_
  rw [Finset.mem_Ico] at hn
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hsize : Nat.size n = k := size_of_mem_stage hk1 hn.1 hn.2
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn.1
  by_contra hnot
  refine hchain n hn1 (hsize ▸ le_trans (le_max_left _ _) hk) (fun j hj => ?_) hbad
  by_contra hg
  exact hnot (Set.mem_biUnion (Finset.mem_range.mpr hj) hg)

/-- **Below the threshold, `𝒞_C` is normal.** -/
theorem normal_of_le_four (C : ℕ) (hC : 1 ≤ C) (hC4 : C ≤ 4) :
    Normal (collatzChampernowne C) :=
  normal_of_stageWordLaw C hC (stageWordLaw_of_le_four C hC hC4)

/-- **Among positive integers, `𝒞_C` is normal exactly for `C ≤ 4`.** -/
theorem normal_iff_le_four (C : ℕ) (hC : 1 ≤ C) :
    Normal (collatzChampernowne C) ↔ C ≤ 4 :=
  ⟨fun h => by
      by_contra hlt
      exact not_normal_of_five_le C (by omega) h,
    normal_of_le_four C hC⟩

end CollatzMoonshot.Conjugacy
