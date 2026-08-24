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

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

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

/-- The Cesàro empirical measure packaged as a `ProbabilityMeasure` (using `N + 1` points so
it is always a probability measure).  Its coercion to `Measure` is `empiricalMeasure x (N+1)`. -/
noncomputable def empiricalPM (x : ℤ_[2]) (N : ℕ) : ProbabilityMeasure ℤ_[2] :=
  ⟨empiricalMeasure x (N + 1), empiricalMeasure_isProbabilityMeasure x (by omega)⟩

@[simp] theorem empiricalPM_toMeasure (x : ℤ_[2]) (N : ℕ) :
    (empiricalPM x N : Measure ℤ_[2]) = empiricalMeasure x (N + 1) := rfl

set_option maxHeartbeats 800000 in
/-- **Krylov–Bogolyubov for the 2-adic Collatz map.**  Every point `x` admits a `T2`-invariant
probability measure, obtained as a weak-* cluster point of its Cesàro empirical measures.

Proof: `ProbabilityMeasure ℤ_[2]` is compact (Prokhorov), so the empirical sequence has a
convergent subsequence `empiricalPM x (ψ k) → μ`.  The push-forwards
`(empiricalPM x (ψ k)).map T2` converge to `μ.map T2` by weak-* continuity of pushforward
(`tendsto_map_of_tendsto_of_continuous`) *and* to `μ` itself: for every bounded continuous `f`,
`∫ f d((empiricalPM x (ψk)).map T2) = ∫ f∘T2 d(empiricalPM x (ψk))`, which differs from
`∫ f d(empiricalPM x (ψk)) → ∫ f dμ` by the telescoping `O(1/ψk) → 0`
(`integral_empiricalMeasure_comp_T2_sub`).  Uniqueness of the weak-* limit forces
`μ.map T2 = μ`, i.e. `IsT2Invariant μ`. -/
theorem exists_isT2Invariant_of_empirical (x : ℤ_[2]) :
    ∃ μ : ProbabilityMeasure ℤ_[2], IsT2Invariant (μ : Measure ℤ_[2]) := by
  obtain ⟨μ, -, hcl⟩ :=
    isCompact_univ.exists_mapClusterPt (f := (atTop : Filter ℕ))
      (u := fun N => empiricalPM x N) (by simp)
  obtain ⟨ψ, hψ_mono, hψ_tendsto⟩ := hcl.tendsto_subseq
  refine ⟨μ, ?_⟩
  rw [isT2Invariant_iff_map_eq]
  -- (empiricalPM x (ψ k)).map T2 → μ.map T2 by continuity of pushforward
  have hmap_cont : Tendsto (fun k => (empiricalPM x (ψ k)).map
      (continuous_T2.measurable.aemeasurable)) atTop
      (𝓝 (μ.map (continuous_T2.measurable.aemeasurable))) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hψ_tendsto continuous_T2
  -- (empiricalPM x (ψ k)).map T2 → μ by the telescoping / integral characterisation
  have hmap_int : Tendsto (fun k => (empiricalPM x (ψ k)).map
      (continuous_T2.measurable.aemeasurable)) atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hchange : ∀ k, ∫ ω, f ω ∂((empiricalPM x (ψ k)).map
        (continuous_T2.measurable.aemeasurable) : Measure ℤ_[2])
        = ∫ ω, f (T2 ω) ∂(empiricalPM x (ψ k) : Measure ℤ_[2]) := by
      intro k
      rw [ProbabilityMeasure.toMeasure_map]
      exact integral_map continuous_T2.measurable.aemeasurable f.continuous.aestronglyMeasurable
    simp_rw [hchange]
    have ha : Tendsto (fun k => ∫ ω, f ω ∂(empiricalPM x (ψ k) : Measure ℤ_[2])) atTop
        (𝓝 (∫ ω, f ω ∂(μ : Measure ℤ_[2]))) :=
      ((ProbabilityMeasure.continuous_integral_continuousMap f).tendsto μ).comp hψ_tendsto
    have hd : Tendsto (fun k => (∫ ω, f (T2 ω) ∂(empiricalPM x (ψ k) : Measure ℤ_[2]))
        - ∫ ω, f ω ∂(empiricalPM x (ψ k) : Measure ℤ_[2])) atTop (𝓝 0) := by
      have hform : ∀ k, (∫ ω, f (T2 ω) ∂(empiricalPM x (ψ k) : Measure ℤ_[2]))
          - ∫ ω, f ω ∂(empiricalPM x (ψ k) : Measure ℤ_[2])
          = (↑(ψ k + 1) : ℝ)⁻¹ * (f (T2^[ψ k + 1] x) - f x) := by
        intro k
        simpa using integral_empiricalMeasure_comp_T2_sub x (ψ k + 1) (⇑f)
      simp_rw [hform, Nat.cast_add, Nat.cast_one]
      have hnull : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹ * (f (T2^[N + 1] x) - f x)) atTop
          (𝓝 0) := by
        apply squeeze_zero_norm (a := fun N : ℕ => ((N : ℝ) + 1)⁻¹ * (2 * ‖f‖))
        · intro N
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          gcongr
          calc ‖f (T2^[N + 1] x) - f x‖ ≤ ‖f (T2^[N + 1] x)‖ + ‖f x‖ := norm_sub_le _ _
            _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
            _ = 2 * ‖f‖ := by ring
        · have hstep : Tendsto (fun N : ℕ => ((N : ℝ) + 1)) atTop atTop :=
            tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
          have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
            tendsto_inv_atTop_zero.comp hstep
          simpa using hinv.mul_const (2 * ‖f‖)
      exact hnull.comp hψ_mono.tendsto_atTop
    simpa using ha.add hd
  have huniq : μ.map (continuous_T2.measurable.aemeasurable) = μ :=
    tendsto_nhds_unique hmap_cont hmap_int
  rw [← ProbabilityMeasure.toMeasure_map μ (continuous_T2.measurable.aemeasurable), huniq]

end CollatzMoonshot
