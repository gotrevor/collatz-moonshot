/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Champernowne
import CollatzMoonshot.Conjugacy.Digits

/-!
# Every `𝒞_C` is disjunctive

Terras's bijection realises every word `u` of length `j` as the first `j` letters of some
`r < 2^j` (`exists_accWord_eq_get`).  Those letters do not see `+ 2^j`, and `n = r + 2^j` has
bit length `j + 1`, so its block in `𝒞_C` has at least `j + 1` letters and starts with `u`.
No Collatz input enters beyond Terras, and the argument is the same for every `C`; above the
threshold `C*` this is a disjunctive sequence believed non-normal for dynamical reasons
(`not_normal_of_earlyArrival`, conditional on `EarlyArrival C`).
-/

namespace CollatzMoonshot.Conjugacy

open CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- **Terras, as words.**  Every word `u` of length `j` is the `j`-letter prefix of the parity
word of some `r < 2^j`. -/
theorem exists_accWord_eq_get (u : List Bool) :
    ∃ r, r < 2 ^ u.length ∧ ∀ j : Fin u.length, accWord r j = u.get j := by
  classical
  let S : Finset ℕ := (Finset.range u.length).filter fun i => u.getD i false = true
  have hS : S ∈ (Finset.range u.length).powerset :=
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  obtain ⟨r, hr, hrS⟩ := onesSet_surjOn u.length (Finset.mem_coe.mpr hS)
  refine ⟨r, Finset.mem_range.mp (Finset.mem_coe.mp hr), fun j => ?_⟩
  have hmem : (j : ℕ) ∈ onesSet r u.length ↔ (j : ℕ) ∈ S := by
    have : onesSet r u.length = S := hrS
    rw [this]
  simp only [mem_onesSet, S, Finset.mem_filter, Finset.mem_range, j.isLt, true_and] at hmem
  have hget : u.getD (j : ℕ) false = u.get j := by
    simp [List.getD_eq_getElem?_getD]
  rw [hget] at hmem
  exact Bool.eq_iff_iff.mpr hmem

/-- **Every `𝒞_C` is disjunctive**: every finite word occurs.  The word `u` of length `j` is the
start of the block of `r + 2^j`, with `r` from Terras's bijection. -/
theorem collatzChampernowne_disjunctive (C : ℕ) : Disjunctive (collatzChampernowne C) := by
  intro u
  obtain ⟨r, hr, hu⟩ := exists_accWord_eq_get u
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = r + 2 ^ u.length :=
    ⟨r + 2 ^ u.length - 1, Nat.sub_add_cancel (Nat.add_pos_right _ (by positivity))⟩
  refine ⟨cum (champLen C) m, fun j => ?_⟩
  have hsize : (j : ℕ) < Nat.size (m + 1) :=
    lt_trans j.isLt (Nat.lt_size.mpr (by rw [hm]; exact Nat.le_add_left _ _))
  have hlen : (j : ℕ) < max C 1 * Nat.size (m + 1) :=
    lt_of_lt_of_le hsize (Nat.le_mul_of_pos_left _ (lt_of_lt_of_le one_pos (le_max_right C 1)))
  rw [collatzChampernowne_apply C m j hlen, hm, accWord_add_two_pow_of_lt j.isLt, hu]

end CollatzMoonshot.Conjugacy
