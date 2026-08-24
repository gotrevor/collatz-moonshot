/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.Rigidity.Padic
import CollatzMoonshot.Rigidity.Invariant

/-!
# Cesàro empirical measures and the Krylov–Bogolyubov step (Front A M2′)

This module builds toward the owed milestone `ParityRigidityW1' → NoDivergentOrbit`
(M2′, `Rigidity/Invariant.lean`).  On a hypothetically divergent orbit the argument
averages the orbit in the compact space `ℤ_[2]`, extracts a weak-* cluster measure, and
uses its `T2`-invariance (Krylov–Bogolyubov) together with `ParityRigidityW1'`.

Here we set up the **Cesàro empirical measure** `empiricalMeasure x N` — the average of the
first `N` Dirac masses along the `T2`-orbit of `x` — and prove its two computational cores:

* `integral_empiricalMeasure` — integrating a continuous function against it is the Birkhoff
  average `N⁻¹ · Σ_{k<N} f (T2^[k] x)`;
* `integral_empiricalMeasure_comp_T2_sub` — the **telescoping** identity
  `∫ f∘T2 dμ_N − ∫ f dμ_N = N⁻¹ · (f (T2^[N] x) − f x)`.  Its right side is `O(1/N)`, which
  is exactly what forces every weak-* cluster point of `μ_N` to be `T2`-invariant (the
  Krylov–Bogolyubov conclusion, assembled next lap via Prokhorov compactness of
  `ProbabilityMeasure ℤ_[2]` and weak-* continuity of `ProbabilityMeasure.map`).

See `PENDING_WORK.md` for the full M2′ decomposition.
-/

open MeasureTheory
open scoped ENNReal

namespace CollatzMoonshot

/-- The **Cesàro empirical measure** of the `T2`-orbit of `x`: the normalised sum of the
first `N` Dirac masses `δ_{T2^[k] x}`.  For `N ≥ 1` it is a probability measure
(`empiricalMeasure_isProbabilityMeasure`). -/
noncomputable def empiricalMeasure (x : ℤ_[2]) (N : ℕ) : Measure ℤ_[2] :=
  (N : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range N, Measure.dirac (T2^[k] x)

/-- For `N ≥ 1` the Cesàro empirical measure is a probability measure: its total mass is
`N⁻¹ · Σ_{k<N} 1 = 1`. -/
theorem empiricalMeasure_isProbabilityMeasure (x : ℤ_[2]) {N : ℕ} (hN : 1 ≤ N) :
    IsProbabilityMeasure (empiricalMeasure x N) := by
  refine ⟨?_⟩
  unfold empiricalMeasure
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  refine ENNReal.inv_mul_cancel ?_ (ENNReal.natCast_ne_top N)
  exact_mod_cast Nat.one_le_iff_ne_zero.mp hN

/-- **Birkhoff-average form of the empirical integral.**  Integrating any `f` against
`empiricalMeasure x N` returns the finite Birkhoff average of `f` along the orbit.  (No
continuity or measurability is needed: this is integration against a finite sum of Diracs.) -/
theorem integral_empiricalMeasure (x : ℤ_[2]) (N : ℕ) (f : ℤ_[2] → ℝ) :
    ∫ y, f y ∂(empiricalMeasure x N) = (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, f (T2^[k] x) := by
  unfold empiricalMeasure
  rw [integral_smul_measure,
    integral_finsetSum_measure (fun k _ => integrable_dirac (by finiteness))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

/-- **The telescoping identity behind Krylov–Bogolyubov.**  The difference between
integrating `f∘T2` and `f` against the empirical measure is `O(1/N)`:
`∫ f∘T2 dμ_N − ∫ f dμ_N = N⁻¹ · (f (T2^[N] x) − f x)`.  As `N → ∞` the right side vanishes,
so any weak-* cluster point `μ` of `μ_N` satisfies `∫ f∘T2 dμ = ∫ f dμ`, i.e. is
`T2`-invariant. -/
theorem integral_empiricalMeasure_comp_T2_sub (x : ℤ_[2]) (N : ℕ) (f : ℤ_[2] → ℝ) :
    (∫ y, f (T2 y) ∂(empiricalMeasure x N)) - (∫ y, f y ∂(empiricalMeasure x N))
      = (N : ℝ)⁻¹ * (f (T2^[N] x) - f x) := by
  rw [integral_empiricalMeasure x N (fun y => f (T2 y)), integral_empiricalMeasure x N f,
    ← mul_sub]
  congr 1
  have key : ∀ k, f (T2 (T2^[k] x)) = f (T2^[k + 1] x) := by
    intro k; rw [Function.iterate_succ_apply']
  simp_rw [key]
  rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => f (T2^[k] x)) N]
  simp

end CollatzMoonshot
