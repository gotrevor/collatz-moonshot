/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.Rigidity.Padic
import CollatzMoonshot.Rigidity.Invariant

/-!
# Cesàro empirical measures and the Krylov–Bogolyubov step (Front A M2′)

This module completes milestone `ParityRigidityW1' → NoDivergentOrbit`
(M2′, `Rigidity/Invariant.lean`).  On a hypothetically divergent orbit the argument
averages the orbit in the compact space `ℤ_[2]`, extracts a weak-* cluster measure, and
uses its `T2`-invariance (Krylov–Bogolyubov) together with `ParityRigidityW1'`.

Here we set up the **Cesàro empirical measure** `empiricalMeasure x N` — the average of the
first `N` Dirac masses along the `T2`-orbit of `x` — and prove its two computational cores:

* `integral_empiricalMeasure` — integrating a continuous function against it is the Birkhoff
  average `N⁻¹ · Σ_{k<N} f (T2^[k] x)`;
* `integral_empiricalMeasure_comp_T2_sub` — the **telescoping** identity
  `∫ f∘T2 dμ_N − ∫ f dμ_N = N⁻¹ · (f (T2^[N] x) − f x)`.  Its right side is `O(1/N)`, which
  is exactly what forces every weak-* cluster point of `μ_N` to be `T2`-invariant. The
  module then proves orbit-closure support, exact parity-frequency transport, a uniform
  sub-sharp `limsup`, and the final divergent-tail contradiction.

See `PENDING_WORK.md` for the full M2′ decomposition.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

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

/-! ## Support of the empirical/cluster measure on the orbit closure (M2′ piece)

For the parity-rigidity keystone W1′ we need the invariant measure to be supported on
`orbitClosure n` (mass `1`).  The empirical measures of the embedded orbit of `↑n` are
literally supported there, and the closed-set Portmanteau bound carries mass `1` to any
weak-* cluster point. -/

/-- Iterating the base intertwining: the `T2`-orbit of `↑n` is the embedded `step`-orbit. -/
theorem T2_iterate_natCast (n : ℕ) (k : ℕ) :
    T2^[k] (n : ℤ_[2]) = ((step^[k] n : ℕ) : ℤ_[2]) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, T2_natCast, Function.iterate_succ_apply']

/-- Each empirical orbit point of `↑n` lies in the orbit closure of `n`. -/
theorem T2_iterate_natCast_mem_orbitClosure (n : ℕ) (k : ℕ) :
    T2^[k] (n : ℤ_[2]) ∈ orbitClosure n := by
  apply subset_closure
  exact ⟨k, by rw [T2_iterate_natCast]⟩

/-- The Cesàro empirical measure of the embedded orbit of `↑n` gives the orbit closure full
mass: every one of its Dirac points sits in the (closed) orbit closure. -/
theorem empiricalMeasure_orbitClosure (n : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    empiricalMeasure (n : ℤ_[2]) N (orbitClosure n) = 1 := by
  have hmeas : MeasurableSet (orbitClosure n) := isClosed_closure.measurableSet
  unfold empiricalMeasure
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  have hterm : ∀ k ∈ Finset.range N,
      Measure.dirac (T2^[k] (n : ℤ_[2])) (orbitClosure n) = 1 := by
    intro k _
    rw [Measure.dirac_apply' _ hmeas,
      Set.indicator_of_mem (T2_iterate_natCast_mem_orbitClosure n k), Pi.one_apply]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  refine ENNReal.inv_mul_cancel ?_ (ENNReal.natCast_ne_top N)
  exact_mod_cast Nat.one_le_iff_ne_zero.mp hN

set_option maxHeartbeats 800000 in
/-- **Cluster measures of the empirical sequence are invariant and orbit-supported.**  If a
subsequence `empiricalPM (↑n) (φ j)` (with `φ → ∞`) converges weak-* to `μ`, then `μ` is
`T2`-invariant *and* supported on `orbitClosure n` (mass `1`).  The invariance is the
Krylov–Bogolyubov telescoping argument (`integral_empiricalMeasure_comp_T2_sub` is `O(1/φ j)`);
the support is the closed-set Portmanteau bound on the (closed) orbit closure.  Stated for an
arbitrary subsequence so that *every* subsequential limit of the odd-frequency is realised as
some invariant measure's odd-mass — the uniformity M2′ piece 2 needs. -/
theorem cluster_isT2Invariant_orbitClosure (n : ℕ) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) {μ : ProbabilityMeasure ℤ_[2]}
    (hconv : Tendsto (fun j => empiricalPM (n : ℤ_[2]) (φ j)) atTop (𝓝 μ)) :
    IsT2Invariant (μ : Measure ℤ_[2]) ∧ (μ : Measure ℤ_[2]) (orbitClosure n) = 1 := by
  set x : ℤ_[2] := (n : ℤ_[2]) with hx
  refine ⟨?_, ?_⟩
  · -- Invariance via the Krylov–Bogolyubov telescoping.
    rw [isT2Invariant_iff_map_eq]
    have hmap_cont : Tendsto (fun k => (empiricalPM x (φ k)).map
        (continuous_T2.measurable.aemeasurable)) atTop
        (𝓝 (μ.map (continuous_T2.measurable.aemeasurable))) :=
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hconv continuous_T2
    have hmap_int : Tendsto (fun k => (empiricalPM x (φ k)).map
        (continuous_T2.measurable.aemeasurable)) atTop (𝓝 μ) := by
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro f
      have hchange : ∀ k, ∫ ω, f ω ∂((empiricalPM x (φ k)).map
          (continuous_T2.measurable.aemeasurable) : Measure ℤ_[2])
          = ∫ ω, f (T2 ω) ∂(empiricalPM x (φ k) : Measure ℤ_[2]) := by
        intro k
        rw [ProbabilityMeasure.toMeasure_map]
        exact integral_map continuous_T2.measurable.aemeasurable f.continuous.aestronglyMeasurable
      simp_rw [hchange]
      have ha : Tendsto (fun k => ∫ ω, f ω ∂(empiricalPM x (φ k) : Measure ℤ_[2])) atTop
          (𝓝 (∫ ω, f ω ∂(μ : Measure ℤ_[2]))) :=
        ((ProbabilityMeasure.continuous_integral_continuousMap f).tendsto μ).comp hconv
      have hd : Tendsto (fun k => (∫ ω, f (T2 ω) ∂(empiricalPM x (φ k) : Measure ℤ_[2]))
          - ∫ ω, f ω ∂(empiricalPM x (φ k) : Measure ℤ_[2])) atTop (𝓝 0) := by
        have hform : ∀ k, (∫ ω, f (T2 ω) ∂(empiricalPM x (φ k) : Measure ℤ_[2]))
            - ∫ ω, f ω ∂(empiricalPM x (φ k) : Measure ℤ_[2])
            = (↑(φ k + 1) : ℝ)⁻¹ * (f (T2^[φ k + 1] x) - f x) := by
          intro k
          simpa using integral_empiricalMeasure_comp_T2_sub x (φ k + 1) (⇑f)
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
        exact hnull.comp hφ
      simpa using ha.add hd
    have huniq : μ.map (continuous_T2.measurable.aemeasurable) = μ :=
      tendsto_nhds_unique hmap_cont hmap_int
    rw [← ProbabilityMeasure.toMeasure_map μ (continuous_T2.measurable.aemeasurable), huniq]
  · -- Support: closed-set Portmanteau carries the full empirical mass to the limit.
    have hclosed : IsClosed (orbitClosure n) := isClosed_closure
    have hlimsup := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv hclosed
    have hone : ∀ k, (empiricalPM x (φ k) : Measure ℤ_[2]) (orbitClosure n) = 1 := by
      intro k
      rw [empiricalPM_toMeasure, hx]
      exact empiricalMeasure_orbitClosure n (by omega)
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞)
        = atTop.limsup
            (fun i => (empiricalPM x (φ i) : Measure ℤ_[2]) (orbitClosure n)) := by
          rw [funext hone]; exact (limsup_const 1).symm
      _ ≤ (μ : Measure ℤ_[2]) (orbitClosure n) := hlimsup

/-- **Krylov–Bogolyubov with support control (M2′).**  Every positive `n` admits a
`T2`-invariant probability measure supported on `orbitClosure n` (mass `1`), as a weak-*
cluster point of the empirical measures of the embedded orbit `↑n`. -/
theorem exists_isT2Invariant_orbitClosure (n : ℕ) :
    ∃ μ : ProbabilityMeasure ℤ_[2],
      IsT2Invariant (μ : Measure ℤ_[2]) ∧ (μ : Measure ℤ_[2]) (orbitClosure n) = 1 := by
  obtain ⟨μ, -, hcl⟩ :=
    isCompact_univ.exists_mapClusterPt (f := (atTop : Filter ℕ))
      (u := fun N => empiricalPM (n : ℤ_[2]) N) (by simp)
  obtain ⟨ψ, hψ_mono, hψ_tendsto⟩ := hcl.tendsto_subseq
  exact ⟨μ, cluster_isT2Invariant_orbitClosure n hψ_mono.tendsto_atTop hψ_tendsto⟩

/-! ## Frequency link: empirical odd-mass = odd-step frequency (M2′ piece 2) -/

/-- An embedded orbit point is odd (in `oddSetZ2`) exactly when the integer iterate is odd. -/
theorem T2_iterate_natCast_mem_oddSetZ2 (n k : ℕ) :
    T2^[k] (n : ℤ_[2]) ∈ oddSetZ2 ↔ step^[k] n % 2 = 1 := by
  rw [T2_iterate_natCast]
  unfold oddSetZ2
  rw [Set.mem_compl_iff, Set.mem_setOf_eq, two_dvd_natCast_iff]
  omega

/-- **The frequency link.**  The empirical odd-mass is exactly the odd-step count over `N`
Dirac points: `μ_N oddSetZ2 = oddSteps n N`.  Together with the total mass `N` this is the
odd-step frequency `oddSteps n N / N`. -/
theorem empiricalMeasure_oddSetZ2 (n : ℕ) (N : ℕ) :
    empiricalMeasure (n : ℤ_[2]) N oddSetZ2 = (N : ℝ≥0∞)⁻¹ * (oddSteps n N : ℝ≥0∞) := by
  have hmeas : MeasurableSet oddSetZ2 := isClopen_oddSetZ2.isClosed.measurableSet
  unfold empiricalMeasure
  rw [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  have hterm : ∀ k, Measure.dirac (T2^[k] (n : ℤ_[2])) oddSetZ2
      = (if step^[k] n % 2 = 1 then (1 : ℝ≥0∞) else 0) := by
    intro k
    rw [Measure.dirac_apply' _ hmeas]
    by_cases h : step^[k] n % 2 = 1
    · rw [Set.indicator_of_mem ((T2_iterate_natCast_mem_oddSetZ2 n k).mpr h), Pi.one_apply,
        if_pos h]
    · rw [Set.indicator_of_notMem (fun hc => h ((T2_iterate_natCast_mem_oddSetZ2 n k).mp hc)),
        if_neg h]
  simp_rw [hterm]
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, oddSteps]; push_cast; ring

/-- The empirical odd-mass of `empiricalPM (↑n) i`, as a real number, is the odd-step
frequency over the first `i+1` orbit points. -/
theorem empiricalPM_oddSetZ2_real (n i : ℕ) :
    (((empiricalPM (n : ℤ_[2]) i) oddSetZ2 : ℝ≥0) : ℝ) = (oddSteps n (i + 1) : ℝ) / (i + 1) := by
  have h1 : ((empiricalPM (n : ℤ_[2]) i) oddSetZ2 : ℝ≥0∞)
      = (i + 1 : ℝ≥0∞)⁻¹ * (oddSteps n (i + 1) : ℝ≥0∞) := by
    rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, empiricalPM_toMeasure,
      empiricalMeasure_oddSetZ2]
    push_cast; ring_nf
  have h2 : (((empiricalPM (n : ℤ_[2]) i) oddSetZ2 : ℝ≥0) : ℝ)
      = ((empiricalPM (n : ℤ_[2]) i) oddSetZ2 : ℝ≥0∞).toReal := by
    rw [ENNReal.coe_toReal]
  rw [h2, h1, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_natCast, ← Nat.cast_add_one]
  rw [div_eq_inv_mul]

/-- **The uniform sub-sharp frequency bound (M2′ piece 2).**  Under `ParityRigidityW1'`, the
`limsup` of the odd-step frequency of any positive orbit is strictly below the sharp drift
threshold.  Every subsequential limit of the frequency is, by Prokhorov + clopen Portmanteau,
realised as the odd-mass of some `T2`-invariant measure supported on `orbitClosure n`, which
W1′ bounds `< sharpThreshold`; `limsup` is such a subsequential limit. -/
theorem limsup_oddFreq_lt_sharp (hW1 : ParityRigidityW1') (n : ℕ) (hn : 1 ≤ n) :
    Filter.limsup (fun i => (oddSteps n (i + 1) : ℝ) / (i + 1)) atTop < sharpThreshold := by
  set g : ℕ → ℝ := fun i => (oddSteps n (i + 1) : ℝ) / (i + 1) with hg
  -- g is bounded in [0,1].
  have hg01 : ∀ i, g i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    refine ⟨by positivity, ?_⟩
    rw [hg, div_le_one (by positivity)]
    have : oddSteps n (i + 1) ≤ i + 1 := by
      have := oddSteps_add_evenSteps n (i + 1); omega
    exact_mod_cast this
  have hbdd : IsBoundedUnder (· ≤ ·) atTop g :=
    ⟨1, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun i => (hg01 i).2)⟩
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop g :=
    IsBounded.isCobounded_le
      ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun i => (hg01 i).1)⟩
  set L : ℝ := Filter.limsup g atTop with hL
  -- L is realised by a subsequence x with x → ∞.
  obtain ⟨x, hxg, hx_top⟩ := exists_seq_tendsto_limsup hcobdd hbdd
  -- Extract a Prokhorov-convergent sub-subsequence of the empiricals along x.
  obtain ⟨μ, -, hcl⟩ :=
    isCompact_univ.exists_mapClusterPt (f := (atTop : Filter ℕ))
      (u := fun j => empiricalPM (n : ℤ_[2]) (x j)) (by simp)
  obtain ⟨σ, hσ_mono, hσ_tendsto⟩ := hcl.tendsto_subseq
  set φ : ℕ → ℕ := fun k => x (σ k) with hφ
  have hφ_top : Tendsto φ atTop atTop := hx_top.comp hσ_mono.tendsto_atTop
  have hconv : Tendsto (fun k => empiricalPM (n : ℤ_[2]) (φ k)) atTop (𝓝 μ) := hσ_tendsto
  obtain ⟨hinv, hsupp⟩ := cluster_isT2Invariant_orbitClosure n hφ_top hconv
  -- W1′ bounds the cluster measure's odd-mass below the sharp threshold.
  have hWbound : ((μ : Measure ℤ_[2]) oddSetZ2).toReal < sharpThreshold :=
    hW1 n hn (μ : Measure ℤ_[2]) inferInstance hinv hsupp
  -- Clopen Portmanteau: empirical odd-mass along φ → μ oddSetZ2 (in ℝ).
  have hport : Tendsto (fun k => ((empiricalPM (n : ℤ_[2]) (φ k)) oddSetZ2 : ℝ))
      atTop (𝓝 ((μ oddSetZ2 : ℝ≥0) : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp
      (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv isClopen_oddSetZ2)
  -- That real limit equals the odd-frequency along φ, whose limit is L.
  have hgφ : Tendsto (fun k => g (φ k)) atTop (𝓝 L) := hxg.comp hσ_mono.tendsto_atTop
  have heq : ∀ k, ((empiricalPM (n : ℤ_[2]) (φ k)) oddSetZ2 : ℝ) = g (φ k) := by
    intro k; rw [empiricalPM_oddSetZ2_real]
  have hport' : Tendsto (fun k => g (φ k)) atTop (𝓝 ((μ oddSetZ2 : ℝ≥0) : ℝ)) := by
    simpa only [heq] using hport
  have hLeq : L = ((μ oddSetZ2 : ℝ≥0) : ℝ) := tendsto_nhds_unique hgφ hport'
  have hcoe : ((μ oddSetZ2 : ℝ≥0) : ℝ) = ((μ : Measure ℤ_[2]) oddSetZ2).toReal := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_toReal]
  rw [hLeq, hcoe]
  exact hWbound

/-- Odd-step count is additive along an orbit shift: the odd steps over `[0, K+k)` split into
those in the prefix `[0,K)` and those of the tail `step^[K] n` over its first `k` steps. -/
theorem oddSteps_iterate_add (n K k : ℕ) :
    oddSteps n (K + k) = oddSteps n K + oddSteps (step^[K] n) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show K + (k + 1) = (K + k) + 1 by omega, oddSteps, oddSteps, ih]
    have hstep : step^[K + k] n = step^[k] (step^[K] n) := by
      rw [Nat.add_comm K k, Function.iterate_add_apply]
    rw [hstep]; ring

/-- **Milestone M2′: parity rigidity forces no divergence.**  `ParityRigidityW1' →
NoDivergentOrbit`.  Assuming a divergent orbit, its odd-step frequency has `limsup`
`< sharpThreshold` (`limsup_oddFreq_lt_sharp`), so a finite floor `N₀` still admits a strictly
larger frequency `freqThreshold N₀` (`exists_freqThreshold_gt`).  The divergent tail
`m = step^[K] n` stays above `N₀` forever (`exists_floor_of_diverges`) and, for all large `k`,
its window frequency stays below `freqThreshold N₀` (the tail frequency is dominated by the
start's, whose limsup is `< freqThreshold N₀`).  The drift estimate `lt_of_oddSteps_freq_lt`
then forces `step^[k] m < m` for all large `k`, so `not_diverges_of_eventually_lt` contradicts
the tail's divergence. -/
theorem parityRigidityW1'_imp_noDivergent :
    ParityRigidityW1' → NoDivergentOrbit := by
  intro hW1 n hn hdiv
  -- Sub-sharp limsup of the odd frequency.
  have hlim := limsup_oddFreq_lt_sharp hW1 n hn
  set L : ℝ := Filter.limsup (fun i => (oddSteps n (i + 1) : ℝ) / (i + 1)) atTop with hLdef
  obtain ⟨N₀, hN₀1, hN₀gt⟩ := exists_freqThreshold_gt hlim
  set c : ℝ := (L + freqThreshold N₀) / 2 with hc
  have hLc : L < c := by rw [hc]; linarith
  have hcf : c < freqThreshold N₀ := by rw [hc]; linarith
  -- Eventually the start-frequency (over all N) is below c.
  have hg01 : ∀ i, (oddSteps n (i + 1) : ℝ) / (i + 1) ≤ 1 := by
    intro i; rw [div_le_one (by positivity)]
    have : oddSteps n (i + 1) ≤ i + 1 := by have := oddSteps_add_evenSteps n (i + 1); omega
    exact_mod_cast this
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun i => (oddSteps n (i + 1) : ℝ) / (i + 1)) :=
    ⟨1, Filter.eventually_map.mpr (Filter.Eventually.of_forall hg01)⟩
  have hev1 : ∀ᶠ i in atTop, (oddSteps n (i + 1) : ℝ) / (i + 1) < c :=
    Filter.eventually_lt_of_limsup_lt (hLdef ▸ hLc) hbdd
  obtain ⟨I, hI⟩ := Filter.eventually_atTop.mp hev1
  have hev2 : ∀ᶠ N in atTop, 1 ≤ N ∧ (oddSteps n N : ℝ) / N < c := by
    refine Filter.eventually_atTop.mpr ⟨I + 1, fun N hN => ⟨by omega, ?_⟩⟩
    have hb := hI (N - 1) (by omega)
    have harg : (N - 1) + 1 = N := Nat.sub_add_cancel (by omega)
    have hd : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      rw [← Nat.cast_add_one, harg]
    rw [harg, hd] at hb
    exact hb
  -- Tail floor: past K the orbit stays ≥ N₀.
  obtain ⟨K, hK⟩ := exists_floor_of_diverges hdiv N₀
  set m : ℕ := step^[K] n with hm
  have hmpos : 1 ≤ m := iterate_step_pos hn K
  have hmdiv : Diverges m := (diverges_iterate_iff (n := n) (K := K)).2 hdiv
  -- Tail window frequency eventually below freqThreshold N₀.
  have htail : ∀ᶠ k in atTop, (oddSteps m k : ℝ) / k < freqThreshold N₀ := by
    -- start-frequency at N = K + k is < c, eventually in k
    have hKk : ∀ᶠ k in atTop, 1 ≤ K + k ∧ (oddSteps n (K + k) : ℝ) / ((K + k : ℕ) : ℝ) < c :=
      (tendsto_atTop_mono (fun k => Nat.le_add_left k K) tendsto_id).eventually hev2
    -- c·(K+k)/k → c < freqThreshold N₀
    have hratio : Tendsto (fun k : ℕ => c * (((K : ℝ) + k) / k)) atTop (𝓝 c) := by
      have h1 : Tendsto (fun k : ℕ => ((K : ℝ) + k) / k) atTop (𝓝 1) := by
        have : (fun k : ℕ => ((K : ℝ) + k) / k) =ᶠ[atTop] (fun k : ℕ => (K : ℝ) / k + 1) := by
          filter_upwards [eventually_gt_atTop 0] with k hk
          have : (k : ℝ) ≠ 0 := by positivity
          field_simp
        rw [tendsto_congr' this]
        simpa using (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)).add
          (tendsto_const_nhds (x := (1 : ℝ)))
      simpa using (tendsto_const_nhds (x := c)).mul h1
    have hlt : ∀ᶠ (k : ℕ) in atTop, c * (((K : ℝ) + k) / k) < freqThreshold N₀ :=
      hratio.eventually (eventually_lt_nhds hcf)
    filter_upwards [hKk, hlt, eventually_gt_atTop 0] with k hk hlt' hk0
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hle : (oddSteps m k : ℝ) ≤ (oddSteps n (K + k) : ℝ) := by
      have : oddSteps n (K + k) = oddSteps n K + oddSteps m k := oddSteps_iterate_add n K k
      have h2 : oddSteps m k ≤ oddSteps n (K + k) := by omega
      exact_mod_cast h2
    calc (oddSteps m k : ℝ) / k ≤ (oddSteps n (K + k) : ℝ) / k := by
            gcongr
      _ = (oddSteps n (K + k) : ℝ) / ((K + k : ℕ) : ℝ) * (((K : ℝ) + k) / k) := by
            have hk0' : (k : ℝ) ≠ 0 := by positivity
            have hKk0 : ((K + k : ℕ) : ℝ) ≠ 0 := by positivity
            push_cast
            field_simp
      _ < c * (((K : ℝ) + k) / k) := by
            apply mul_lt_mul_of_pos_right hk.2
            positivity
      _ < freqThreshold N₀ := hlt'
  -- Combine floor + frequency into eventual descent of the tail.
  have hdesc : ∀ᶠ k in atTop, step^[k] m < m := by
    filter_upwards [htail, eventually_gt_atTop 0] with k hfreq hk0
    have hfloor : ∀ j < k, N₀ ≤ step^[j] m := by
      intro j _
      rw [hm, ← Function.iterate_add_apply]
      exact hK (j + K) (by omega)
    exact lt_of_oddSteps_freq_lt hmpos hN₀1 hk0 hfloor hfreq
  obtain ⟨K', hK'⟩ := Filter.eventually_atTop.mp hdesc
  exact not_diverges_of_eventually_lt ⟨K', hK'⟩ hmdiv

end CollatzMoonshot
