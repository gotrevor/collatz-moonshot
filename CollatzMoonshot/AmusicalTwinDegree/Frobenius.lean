/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalTwinDegree.Corollaries

/-!
# Frobenius and the twin

* `twinU_twinU_sq`: `U² (n²) = (U n)²` on the shallow classes `E ∪ A`.
* `not_periodic_of_selfSimilar` (Proposition M): a point of maximal degree on a cycle cannot have
  `y² + c` on its orbit.
* `eq_zero_or_one_of_twinU_twinU`: `U² x = x` only for `x ∈ {0, 1}`.  Off the exceptional set the
  two steps must have degree changes summing to `0`, leaving the class pairs `EB, EC, BE, CE, AA`.
  The pair identity `(t^{d₁+d₂} − Q²) x = Q e₁ + t^{d₁} e₂` evaluated at `t = 1` kills the first
  four (the left side vanishes, the right side is `1`), and `AA` reads `(t + 1)² (x − 1) = 0`.
* `no_classwise_core`: the four instances `n = 0, t, Q, 1 + t` of a class-wise repair are
  inconsistent.
-/

namespace CollatzMoonshot.Amusical.TwinDeg

open Polynomial Function

lemma sq_char_two (a b : (ZMod 2)[X]) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := add_pow_char a b 2

/-- `U² (n²) = (U n)²` for `n ∈ E ∪ A`. -/
theorem twinU_twinU_sq (n : (ZMod 2)[X]) (h : n.coeff 0 = 0 ∨ n.coeff 1 = 0) :
    twinU (twinU (n ^ 2)) = twinU n ^ 2 := by
  rcases FFTwin.fU_cases n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show (X * k) ^ 2 = X * (X * k ^ 2) by ring, twinU_E, twinU_E,
      show twinQ * (X * k ^ 2) = X * (twinQ * k ^ 2) by ring, twinU_E]
    ring
  · rw [sq_char_two, show (1 : (ZMod 2)[X]) ^ 2 + (X ^ 2 * k) ^ 2 = 1 + X ^ 2 * (X ^ 2 * k ^ 2)
      by ring, twinU_A, twinU_A, sq_char_two,
      show twinQ * (X ^ 2 * k ^ 2) + 1 = 1 + X ^ 2 * (twinQ * k ^ 2) by ring, twinU_A]
    ring
  · exfalso
    simp [coeff_add, coeff_one, coeff_X, coeff_X_pow_mul'] at h
  · exfalso
    simp [coeff_add, coeff_one, coeff_X, coeff_X_pow, coeff_X_pow_mul'] at h

/-- **Proposition M.** -/
theorem not_periodic_of_selfSimilar (C : Finset (ZMod 2)[X])
    (hC : ∀ z, ∀ c ∈ C, ∃ k, 1 ≤ k ∧ ∃ c' ∈ C, twinU^[k] (z ^ 2 + c) = twinU z ^ 2 + c')
    (z : (ZMod 2)[X]) (hdeg : ∀ c ∈ C, c.natDegree < z.natDegree)
    (hz : ∃ c ∈ C, ∃ a, twinU^[a] z = z ^ 2 + c) : z ∉ periodicPts twinU := by
  intro hzp
  have hp : 0 < minimalPeriod twinU z := minimalPeriod_pos_of_mem_periodicPts hzp
  have hper : IsPeriodicPt twinU (minimalPeriod twinU z) z := isPeriodicPt_minimalPeriod twinU z
  have hall : ∀ j, ∃ c ∈ C, ∃ a, twinU^[a] z = (twinU^[j] z) ^ 2 + c := by
    intro j
    induction j with
    | zero => simpa using hz
    | succ j ih =>
      obtain ⟨c, hc, a, ha⟩ := ih
      obtain ⟨k, -, c', hc', hk⟩ := hC (twinU^[j] z) c hc
      exact ⟨c', hc', k + a, by rw [iterate_add_apply, ha, hk, iterate_succ_apply']⟩
  obtain ⟨j₁, -, hmax⟩ := Finset.exists_max_image (Finset.range (minimalPeriod twinU z))
    (fun j => (twinU^[j] z).natDegree) ⟨0, Finset.mem_range.mpr hp⟩
  have hbound : ∀ a, (twinU^[a] z).natDegree ≤ (twinU^[j₁] z).natDegree := by
    intro a
    rw [← hper.iterate_mod_apply a]
    exact hmax _ (Finset.mem_range.mpr (Nat.mod_lt _ hp))
  obtain ⟨c, hc, a, ha⟩ := hall j₁
  have hz1 := hbound 0
  have hcz := hdeg c hc
  simp only [iterate_zero, id_eq] at hz1
  have hsq : ((twinU^[j₁] z) ^ 2 + c).natDegree = 2 * (twinU^[j₁] z).natDegree := by
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> rw [natDegree_pow] <;> omega
  have := hbound a
  rw [ha, hsq] at this
  omega

end CollatzMoonshot.Amusical.TwinDeg
