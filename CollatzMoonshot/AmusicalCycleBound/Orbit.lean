/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalCycleBound.Step

/-! # Orbit bookkeeping for the cycle-minimum reduction -/

namespace CollatzMoonshot.Amusical

theorem amusical_iterate_neg (x : ℤ) (j : ℕ) : amusical^[j] (-x) = -amusical^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, amusical_neg]

theorem amusical_pos_of_pos {x : ℤ} (hx : 0 < x) : 0 < amusical x := by
  unfold amusical; split_ifs <;> omega

theorem amusical_iterate_pos {x : ℤ} (hx : 0 < x) (j : ℕ) : 0 < amusical^[j] x := by
  induction j with
  | zero => exact hx
  | succ j ih => rw [Function.iterate_succ_apply']; exact amusical_pos_of_pos ih

theorem amusical_mem_knownCycleMembers {x : ℤ} (hx : x ∈ knownCycleMembers) :
    amusical x ∈ knownCycleMembers := by
  revert x hx; decide

theorem amusical_iterate_mem_knownCycleMembers {x : ℤ} (hx : x ∈ knownCycleMembers) (j : ℕ) :
    amusical^[j] x ∈ knownCycleMembers := by
  induction j with
  | zero => exact hx
  | succ j ih => rw [Function.iterate_succ_apply']; exact amusical_mem_knownCycleMembers ih

/-- A point of period `P` for `U` has period `P` for `U⁻¹`. -/
theorem amusicalInv_iterate_of_cycle {n : ℤ} {P : ℕ} (h : amusical^[P] n = n) :
    amusicalInv^[P] n = n := by
  have hl : Function.LeftInverse amusicalInv^[P] amusical^[P] :=
    Function.LeftInverse.iterate amusicalInv_amusical P
  conv_lhs => rw [← h]
  exact hl n

theorem stepBits_le_two (x : ℤ) : stepBits x ≤ 2 := by
  unfold stepBits; split_ifs <;> omega

theorem sum_stepBits_le (x : ℤ) (p : ℕ) :
    ∑ j ∈ Finset.range p, stepBits (amusical^[j] x) ≤ 2 * p := by
  calc ∑ j ∈ Finset.range p, stepBits (amusical^[j] x) ≤ ∑ _j ∈ Finset.range p, 2 :=
        Finset.sum_le_sum fun j _ => stepBits_le_two _
    _ = 2 * p := by simp [mul_comm]

/-- The minimum of a periodic orbit: a point `n` of the orbit of `y`, from which `y` is reached,
lying below every iterate of `n`. -/
theorem exists_orbit_min {f : ℤ → ℤ} {y : ℤ} {p : ℕ} (hp : 0 < p) (hy : f^[p] y = y) :
    ∃ n, (∃ j, f^[j] n = y) ∧ (∃ j, f^[j] y = n) ∧ f^[p] n = n ∧ ∀ j, n ≤ f^[j] n := by
  have hne : ((Finset.range p).image fun j => f^[j] y).Nonempty := by
    simp only [Finset.image_nonempty, Finset.nonempty_range_iff]; omega
  set n := ((Finset.range p).image fun j => f^[j] y).min' hne with hn
  have hmem := Finset.min'_mem _ hne
  rw [← hn, Finset.mem_image] at hmem
  obtain ⟨j0, hj0, hj0n⟩ := hmem
  have hj0' : j0 < p := Finset.mem_range.mp hj0
  have hyper : Function.IsPeriodicPt f p y := hy
  refine ⟨n, ⟨p - j0, ?_⟩, ⟨j0, hj0n⟩, ?_, ?_⟩
  · rw [← hj0n, ← Function.iterate_add_apply, Nat.sub_add_cancel hj0'.le]; exact hy
  · rw [← hj0n, ← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hy]
  · intro j
    have hmod : f^[j] n = f^[(j + j0) % p] y := by
      rw [← hj0n, ← Function.iterate_add_apply, hyper.iterate_mod_apply]
    rw [hmod, hn]
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.mod_lt _ hp), rfl⟩

end CollatzMoonshot.Amusical
