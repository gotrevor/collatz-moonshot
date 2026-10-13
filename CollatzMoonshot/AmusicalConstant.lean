/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindow

/-!
# The orbit-minimum constant of the amusical permutation

`minimaConstant = exp(-Σ_{k≥1} E[min(1, 2^(k+O_k)/3^k)] / k) ≈ 0.049780`, `O_k ~ Bin(k, 1/2)`:
the conjectured density of orbit minima, and (given `windowMinDensity` and
`WindowDensityLimit`) an upper bound on it.  `windowMinDensity` is proved, so the bound rests on
`WindowDensityLimit` alone.
-/

namespace CollatzMoonshot.Amusical

/-! ## The constant: Spitzer's formula plus Haar duality -/

/-- The `k`-th Spitzer term `E[min(1, 2^(k+O)/3^k)]`, `O ~ Bin(k, 1/2)` the odd steps: the
probability, summed over both directions, that the walk is below its start after `k` steps.
Forward this is `P(S_k ≤ 0)`; backward, by Haar duality, `P(B_k ≤ 0) = E[e^{-S_k}; S_k > 0]`. -/
noncomputable def spitzerTerm (k : ℕ) : ℝ :=
  ∑ o ∈ Finset.range (k + 1),
    (Nat.choose k o : ℝ) / 2 ^ k * min 1 ((2 : ℝ) ^ (k + o) / 3 ^ k)

/-- The conjectured density of orbit minima, `exp(-Σ_{k≥1} spitzerTerm k / k) ≈ 0.049780`. -/
noncomputable def minimaConstant : ℝ :=
  Real.exp (-∑' k : ℕ, spitzerTerm (k + 1) / (k + 1))

/-- **The window densities decrease to `minimaConstant`** (proved: `windowDensityLimit` in
`AmusicalSpitzer.lean`, 2026-10-13).  Sparre Andersen's theorem gives
`lim fwdSurv L = exp(-Σ P(S_k ≤ 0)/k)` and `lim bwdSurv L = exp(-Σ P(B_k ≤ 0)/k)`
for the two multiplicative walks (no ties: `3^k ≠ 2^m`).  The backward walk is the forward walk
reversed and tilted by `e^{-S}` (the Haar balance `E[e^{-S_1}] = 1`), so the two series merge
into `Σ spitzerTerm k / k`.  Numerics (`scripts/amusical/spitzer.py`, 4000 terms):
`p_f = 0.210136`, `p_b = 0.236892`, product `0.049780`, matching the lattice computation and
the measured minima density `0.049957` on `1..10^6` within one standard error. -/
def WindowDensityLimit : Prop :=
  Filter.Tendsto (fun L : ℕ => ((fwdSurv L * bwdSurv L : ℚ) : ℝ)) Filter.atTop
    (nhds minimaConstant)

open Classical in
/-- Orbit minima have upper density at most `minimaConstant`, given the window densities and
their limit (both proved; the unconditional form is `orbitMin_density_le_minimaConstant'`). -/
theorem orbitMin_density_le_minimaConstant (hlim : WindowDensityLimit) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X ≤ minimaConstant + ε := by
  obtain ⟨L, hL⟩ := (hlim.eventually (gt_mem_nhds (by linarith : minimaConstant < minimaConstant
    + ε / 2))).exists
  filter_upwards [orbitMin_density_le L (by linarith : (0 : ℝ) < ε / 2)] with X hX
  linarith

open Classical in
/-- **Conjecture (2026-10-13), sharp form of `AmusicalMinimaDensity`.**  The orbit minima have
natural density exactly `minimaConstant`. -/
def AmusicalMinimaDensityExact : Prop :=
  Filter.Tendsto
    (fun X : ℕ => (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X)
    Filter.atTop (nhds minimaConstant)

open Classical in
/-- **Unconditional:** orbit minima have upper density at most `4/27 ≈ 0.148`
(`windowMinDensity 4` with `windowDensity_values`).  Longer windows give
`δ₁₀ ≈ 0.088`, `δ₄₀ ≈ 0.057`, decreasing to `minimaConstant ≈ 0.0498`. -/
theorem orbitMin_density_le_four_twentySevenths {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X ≤ 4 / 27 + ε := by
  have h4 : ((fwdSurv 4 * bwdSurv 4 : ℚ) : ℝ) = 4 / 27 := by
    rw [windowDensity_values.2.2.2]; norm_num
  simpa [h4] using orbitMin_density_le 4 hε

end CollatzMoonshot.Amusical
