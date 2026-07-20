/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.Basic

/-!
# Assumed: Tao 2019 - almost all orbits attain almost bounded values

Tier: THEOREM-grade - and more: **we formalized this one ourselves**
([gotrevor/tao-collatz](https://github.com/gotrevor/tao-collatz), complete
2026-07-15, axiom-clean, comparator-verified).  Before that repo existed this
axiom would have been the "assume the frontier" move; now it is a *citation*.
The statement here is re-rendered self-contained (log density via harmonic
weights), so it may differ from the ratified repo statement in inessential
renderings - the honest upgrade path is to `require` tao-collatz and prove this
axiom from `tao_collatz`, retiring it.
-/

namespace CollatzMoonshot

open Filter

/-- The minimum value attained by the orbit of `n`. -/
noncomputable def orbitMin (n : ℕ) : ℕ := sInf (Set.range fun k => step^[k] n)

/-- Logarithmically-weighted partial density of `A ⊆ ℕ` up to `x`:
`(log x)⁻¹ · ∑_{n ∈ A, 1 ≤ n ≤ x} 1/n`. -/
noncomputable def logDensityUpTo (A : Set ℕ) (x : ℕ) : ℝ :=
  (Real.log x)⁻¹ * ∑ n ∈ Finset.Icc 1 x, A.indicator (fun m => (m : ℝ)⁻¹) n

/-- `A ⊆ ℕ` has logarithmic density `1`. -/
def HasLogDensityOne (A : Set ℕ) : Prop :=
  Tendsto (logDensityUpTo A) atTop (nhds 1)

namespace Assumed

/-- **[ASSUMED - proved by us upstream]** Tao 2019, Theorem 1.3: for any
`f : ℕ → ℝ` tending to infinity, `orbitMin n < f n` for almost all `n` in
logarithmic density.

Provenance: Tao, *Almost all orbits of the Collatz map attain almost bounded
values* (arXiv:1909.03562).  Formalized end-to-end in gotrevor/tao-collatz
(`tao_collatz`, kernel-verified 2026-07-15).  Mind barrier 2 of `APPROACHES.md`
when consuming this: log density 1 is qualitatively short of "all n", and no
constant-tightening crosses that gap. -/
axiom tao_2019_almost_bounded :
    ∀ f : ℕ → ℝ, Tendsto f atTop atTop →
      HasLogDensityOne {n : ℕ | 1 ≤ n ∧ (orbitMin n : ℝ) < f n}

end Assumed

end CollatzMoonshot
