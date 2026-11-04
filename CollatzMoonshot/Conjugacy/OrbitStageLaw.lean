/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitHeightLaw

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

/-- **The orbit word law over one stage, for `C ≤ 4`.**  Believed, 88%. -/
theorem stageWordLaw_of_le_four (C : ℕ) (hC : 1 ≤ C) (hC4 : C ≤ 4) : StageWordLaw C := by
  sorry

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
