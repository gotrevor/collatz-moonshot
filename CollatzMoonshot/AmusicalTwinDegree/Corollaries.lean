/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalTwinDegree.Step

/-!
# Corollaries of Theorem D

* (D-iii) `period_lower_bound`: take `y` of minimal degree on the cycle of `x`.  The degree moves
  by at most one per step, and `x` is `j₀` steps after and `p − j₀` steps before `y`, so
  `2 deg x ≤ 2 deg y + p ≤ 2 (p + 2) + p`.
* (D-i) `cycleMins_finite`: the minima of valuation class `v` have degree `≤ 2^v + 2`, and over
  `𝔽₂` there are finitely many such polynomials (`finite_natDegree_le`).
-/

namespace CollatzMoonshot.Amusical.TwinDeg

open Polynomial Function

/-- Every point of a cycle has a cycle minimum `j₀` steps before it. -/
lemma exists_cycleMin (x : (ZMod 2)[X]) (hx : x ∈ periodicPts twinU) :
    ∃ j₀ < minimalPeriod twinU x,
      ∀ j, (twinU^[j₀] x).natDegree ≤ (twinU^[j] (twinU^[j₀] x)).natDegree := by
  set p := minimalPeriod twinU x
  have hp : 0 < p := minimalPeriod_pos_of_mem_periodicPts hx
  have hper : IsPeriodicPt twinU p x := isPeriodicPt_minimalPeriod twinU x
  obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image (Finset.range p)
    (fun j => (twinU^[j] x).natDegree) ⟨0, Finset.mem_range.mpr hp⟩
  refine ⟨j₀, Finset.mem_range.mp hj₀, fun j => ?_⟩
  rw [← iterate_add_apply, ← hper.iterate_mod_apply (j + j₀)]
  exact hmin _ (Finset.mem_range.mpr (Nat.mod_lt _ hp))

/-- **D-iii.**  `2 deg x ≤ 3p + 4` for a periodic `x` of exact period `p`. -/
theorem period_lower_bound (x : (ZMod 2)[X]) (hx : x ∈ periodicPts twinU) :
    2 * x.natDegree ≤ 3 * minimalPeriod twinU x + 4 := by
  by_cases hxe : x ∈ exc
  · have := natDegree_le_two_of_mem_exc hxe; omega
  have hp : 0 < minimalPeriod twinU x := minimalPeriod_pos_of_mem_periodicPts hx
  obtain ⟨j₀, hj₀, hmin⟩ := exists_cycleMin x hx
  have hyp : twinU^[j₀] x ∈ periodicPts twinU :=
    mk_mem_periodicPts hp ((isPeriodicPt_minimalPeriod twinU x).apply_iterate j₀)
  have hD := cycleMin_natDegree_le _ hyp hmin
  rw [minimalPeriod_apply_iterate hx j₀] at hD
  have hvle : 2 ^ padicValNat 2 (minimalPeriod twinU x) ≤ minimalPeriod twinU x :=
    Nat.le_of_dvd hp pow_padicValNat_dvd
  have hye : twinU^[j₀] x ∉ exc := by rwa [iterate_mem_exc_iff]
  have h1 := (natDegree_iterate_le x hxe j₀).2
  have hback : twinU^[minimalPeriod twinU x - j₀] (twinU^[j₀] x) = x := by
    rw [← iterate_add_apply, Nat.sub_add_cancel hj₀.le]; exact iterate_minimalPeriod
  have h2 := (natDegree_iterate_le _ hye (minimalPeriod twinU x - j₀)).1
  rw [hback] at h2
  omega

/-- Over `𝔽₂`, finitely many polynomials have degree at most `n`. -/
lemma finite_natDegree_le (n : ℕ) : {f : (ZMod 2)[X] | f.natDegree ≤ n}.Finite := by
  refine (Set.finite_range
    (fun g : Fin (n + 1) → ZMod 2 => ∑ i : Fin (n + 1), monomial (i : ℕ) (g i))).subset ?_
  intro f hf
  refine ⟨fun i => f.coeff i, ?_⟩
  simp only
  rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (f.coeff i)) (n + 1)]
  exact (as_sum_range' f (n + 1) (Nat.lt_succ_of_le hf)).symm

/-- **D-i.** -/
theorem cycleMins_finite (v : ℕ) :
    {x : (ZMod 2)[X] | x ∈ periodicPts twinU ∧
      padicValNat 2 (minimalPeriod twinU x) = v ∧
      ∀ j, x.natDegree ≤ (twinU^[j] x).natDegree}.Finite := by
  refine (finite_natDegree_le (2 ^ v + 2)).subset ?_
  rintro x ⟨hx, rfl, hmin⟩
  exact cycleMin_natDegree_le x hx hmin

end CollatzMoonshot.Amusical.TwinDeg
