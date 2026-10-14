/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical

namespace CollatzMoonshot.Amusical

open Classical in
/-- Exact reciprocal-weight transport from even integers to multiples of three. -/
theorem sum_multiples_three_transport {S : Set ℤ}
    (hS : ∀ x, amusical x ∈ S ↔ x ∈ S) (N : ℕ) :
    ∑ m ∈ (Finset.Icc (1 : ℤ) (3 * (N / 2))).filter
        (fun m ↦ m ∈ S ∧ 3 ∣ m), (1 : ℝ) / m =
      (2 / 3 : ℝ) * ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter
        (fun n ↦ n ∈ S ∧ 2 ∣ n), (1 : ℝ) / n := by
  classical
  symm
  rw [Finset.mul_sum]
  apply Finset.sum_bij (fun n _ ↦ amusical n)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    rcases hn with ⟨⟨hn1, hnN⟩, hnS, hn2⟩
    obtain ⟨k, rfl⟩ := hn2
    rw [amusical_two_mul]
    constructor
    · constructor <;> omega
    · exact ⟨by simpa [amusical_two_mul] using (hS _).2 hnS, dvd_mul_right 3 k⟩
  · intro a ha b hb hab
    exact amusical_injective hab
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    rcases hm with ⟨⟨hm1, hmN⟩, hmS, hm3⟩
    obtain ⟨k, rfl⟩ := hm3
    refine ⟨2 * k, ?_, amusical_two_mul k⟩
    · constructor
      · constructor <;> omega
      · exact ⟨(hS _).1 (by simpa [amusical_two_mul] using hmS), dvd_mul_right 2 k⟩
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn with ⟨⟨hn1, hnN⟩, hnS, hn2⟩
    obtain ⟨k, rfl⟩ := hn2
    rw [amusical_two_mul]
    norm_num
    field_simp

end CollatzMoonshot.Amusical
