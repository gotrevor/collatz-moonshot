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

/-- Normality implies logarithmic normality, by partial summation.  Confidence 95%. -/
theorem logNormal_of_normal (w : ℕ → Bool) (h : Normal w) : LogNormal w := by
  sorry

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

/-- **The orbit word law gives logarithmic normality.**  The word of `n` carries log-weight `≈ 1 / n`,
straddling windows are `O(1 / log n)` of it, and letters are bounded, so bad starts of density `0`
contribute nothing.  Confidence 90%. -/
theorem logNormal_of_orbitWordLaw (C : ℕ) (hC : 1 ≤ C) (h : OrbitWordLaw C) :
    LogNormal (collatzChampernowne C) := by
  sorry

/-- **Above the threshold, `𝒞_C` is not normal even in logarithmic density.**  `drift_total` holds at
every word end, and partial summation carries the linear inequality to logarithmic frequencies, whose
limit would again read `0.5 ≤ 0.4966`.  Confidence 90%. -/
theorem not_logNormal_of_five_le (C : ℕ) (hC : 5 ≤ C) : ¬ LogNormal (collatzChampernowne C) := by
  sorry

end CollatzMoonshot.Conjugacy
