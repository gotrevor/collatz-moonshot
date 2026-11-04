/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import TaoCollatz.Sec5.Stabilization
import CollatzMoonshot.Conjugacy.ChampernowneLog

/-!
# The orbit word law, from Tao's stabilisation

For `C ≤ 4`, almost every start in logarithmic density has the right frequency of every word among
its first `C log₂ n` parity letters (`orbitWordLaw_of_le_four`), so `𝒞_C` is normal in logarithmic
density (`logNormal_of_le_four`).  The proof chains Tao 2019 Proposition 1.11 (`stabilization_atCX`)
over scales `x_(j+1) = x_j^(1/α)`, down to `N^(1/10)`.  Research note §16.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- **Frozen target.  Believed, 85%, given (1.20), which `stabilization_atCX` proves.** -/
theorem orbitWordLaw_of_le_four (C : ℕ) (hC : 1 ≤ C) (hC4 : C ≤ 4) : OrbitWordLaw C := by
  sorry

/-- **Below the threshold, `𝒞_C` is normal in logarithmic density.** -/
theorem logNormal_of_le_four (C : ℕ) (hC : 1 ≤ C) (hC4 : C ≤ 4) :
    LogNormal (collatzChampernowne C) :=
  logNormal_of_orbitWordLaw C hC (orbitWordLaw_of_le_four C hC hC4)

end CollatzMoonshot.Conjugacy
