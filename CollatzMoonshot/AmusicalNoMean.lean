/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical

/-!
# No mean on `ℤ` is invariant under both `n ↦ n + 1` and `U` (research §51)

Round-4 ideation (2026-10-14, Fable, "Theorem N") read Klamkin (a) as a double-coset count for the
group `Γ = ⟨T, U⟩ ≤ Sym(ℤ)`, `T n = n + 1`, and observed that this action is non-amenable: a
finitely additive probability mean invariant under `T` gives the even integers mass `1/2` and the
multiples of 3 mass `1/3`, but `U` maps the evens onto the multiples of 3.

So every quasi-invariant averaging structure on `ℤ` that `T` respects is broken by `U`; the
amusical permutation is a generator of a non-amenable two-generator subgroup of `RCWA(ℤ)`.

* `amusical_image_even`: `U` maps the even integers onto the multiples of 3.
* `no_translation_amusical_invariant_mean`: no finitely additive probability mean on `ℤ` is
  invariant under both `n ↦ n + 1` and `U`.
-/

namespace CollatzMoonshot.Amusical

/-- A finitely additive probability mean on the subsets of `ℤ`. -/
structure IntMean where
  /-- The mass of a set. -/
  m : Set ℤ → ℝ
  /-- Total mass one. -/
  univ : m Set.univ = 1
  /-- Finite additivity. -/
  add : ∀ s t, Disjoint s t → m (s ∪ t) = m s + m t

/-- **Target.**  `U` maps the even integers onto the multiples of 3. -/
theorem amusical_image_even : amusical '' {n | 2 ∣ n} = {n | 3 ∣ n} := by
  ext m
  constructor
  · rintro ⟨n, ⟨k, rfl⟩, rfl⟩
    rw [amusical_two_mul]
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨2 * k, ⟨k, rfl⟩, amusical_two_mul k⟩

private theorem image_add_one (s : Set ℤ) : (· + 1) '' s = {n | n - 1 ∈ s} := by
  ext n
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨n - 1, h, by ring⟩

/-- **Target (Theorem N).**  No finitely additive probability mean on `ℤ` is invariant under both
the translation `n ↦ n + 1` and the amusical permutation. -/
theorem no_translation_amusical_invariant_mean (μ : IntMean)
    (hT : ∀ s, μ.m ((· + 1) '' s) = μ.m s) (hU : ∀ s, μ.m (amusical '' s) = μ.m s) : False := by
  -- the evens have mass `1/2`
  have hE : μ.m {n | 2 ∣ n} = 1 / 2 := by
    have h1 := hT {n | 2 ∣ n}
    rw [image_add_one] at h1
    have h2 := μ.add {n | 2 ∣ n} {n | n - 1 ∈ {n : ℤ | 2 ∣ n}} (by
      rw [Set.disjoint_left]; intro n h h'; simp only [Set.mem_ofPred_eq] at h h'; omega)
    have h3 : {n : ℤ | 2 ∣ n} ∪ {n | n - 1 ∈ {n : ℤ | 2 ∣ n}} = Set.univ := by
      ext n; simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]; omega
    rw [h3, μ.univ] at h2
    linarith
  -- the multiples of 3 have mass `1/3`
  have hD : μ.m {n | 3 ∣ n} = 1 / 3 := by
    have h1 := hT {n | 3 ∣ n}
    have h1' := hT {n | n - 1 ∈ {n : ℤ | 3 ∣ n}}
    rw [image_add_one] at h1 h1'
    have h2 := μ.add {n | 3 ∣ n} {n | n - 1 ∈ {n : ℤ | 3 ∣ n}} (by
      rw [Set.disjoint_left]; intro n h h'; simp only [Set.mem_ofPred_eq] at h h'; omega)
    have h4 := μ.add ({n | 3 ∣ n} ∪ {n | n - 1 ∈ {n : ℤ | 3 ∣ n}})
      {n | n - 1 ∈ {n | n - 1 ∈ {n : ℤ | 3 ∣ n}}} (by
      rw [Set.disjoint_left]; intro n h h'
      simp only [Set.mem_union, Set.mem_ofPred_eq] at h h'; omega)
    have h3 : ({n : ℤ | 3 ∣ n} ∪ {n | n - 1 ∈ {n : ℤ | 3 ∣ n}}) ∪
        {n | n - 1 ∈ {n | n - 1 ∈ {n : ℤ | 3 ∣ n}}} = Set.univ := by
      ext n; simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]; omega
    rw [h3, μ.univ, h2] at h4
    linarith
  have h := hU {n | 2 ∣ n}
  rw [amusical_image_even, hE, hD] at h
  norm_num at h

end CollatzMoonshot.Amusical
