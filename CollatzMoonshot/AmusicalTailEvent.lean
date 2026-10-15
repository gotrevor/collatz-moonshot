/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Infinite orbits survive successor swaps, so (a) is a tail event (Lemma E, research §48)

From the 2026-10-14 round-2 ideation lap (Fable).  For a permutation `σ` of `ℕ`, swapping the
successors of two points (`σ * swap a b`, so `a ↦ σ b` and `b ↦ σ a`) either merges two orbits or
splits one into two.  A merge of an infinite orbit with anything stays infinite; two infinite
orbits stay two infinite orbits; splitting an infinite orbit leaves one infinite orbit and one
finite cycle.  So the number of infinite orbits never changes
(`encard_infinitePermOrbits_mul_swap`), and the total number of orbits changes by at most one
(`infinite_permOrbits_mul_swap_iff`).  Hence "infinitely many orbits" is invariant under any
finite set of successor swaps: in a random perturbation family of `U` it is a tail event, so it
has probability `0` or `1`.
-/

namespace CollatzMoonshot.Amusical

/-- The orbit of `x` under the permutation `σ` of `ℕ`. -/
def natPermOrbit (σ : Equiv.Perm ℕ) (x : ℕ) : Set ℕ := Set.range fun j : ℤ => (σ ^ j) x

/-- The orbits of `σ`. -/
def natPermOrbits (σ : Equiv.Perm ℕ) : Set (Set ℕ) := {O | ∃ x, O = natPermOrbit σ x}

/-- The infinite orbits of `σ`. -/
def infiniteNatPermOrbits (σ : Equiv.Perm ℕ) : Set (Set ℕ) :=
  {O | ∃ x, O = natPermOrbit σ x ∧ O.Infinite}

/-- **Target (Lemma E).**  A successor swap does not change the number of infinite orbits. -/
theorem encard_infinitePermOrbits_mul_swap (σ : Equiv.Perm ℕ) (a b : ℕ) :
    (infiniteNatPermOrbits (σ * Equiv.swap a b)).encard = (infiniteNatPermOrbits σ).encard := by
  sorry

/-- **Target.**  A successor swap does not change whether there are infinitely many orbits. -/
theorem infinite_permOrbits_mul_swap_iff (σ : Equiv.Perm ℕ) (a b : ℕ) :
    (natPermOrbits (σ * Equiv.swap a b)).Infinite ↔ (natPermOrbits σ).Infinite := by
  sorry

/-- **Target.**  The same for any finite list of successor swaps. -/
theorem infinite_permOrbits_mul_swaps_iff (σ : Equiv.Perm ℕ) (l : List (ℕ × ℕ)) :
    (natPermOrbits (σ * (l.map fun p => Equiv.swap p.1 p.2).prod)).Infinite ↔
      (natPermOrbits σ).Infinite := by
  sorry

end CollatzMoonshot.Amusical
