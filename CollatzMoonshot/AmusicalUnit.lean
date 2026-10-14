/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalSurvivorSeparation
import CollatzMoonshot.AmusicalContinuousReversor

/-!
# Multiplicative symmetries: transport is free, existence is a 2-adic irrationality question

The 2026-10-14 "ringunit" agent asked for a partial multiplicative symmetry of `U` that moves
orbits to orbits, in the spirit of Theorem W (research §22).

**Proposition T (agent; research §28).**  A map that commutes with `U` along a forward orbit tail
and is asymptotically multiplication by `u ∉ ±2^ℤ 3^ℤ` sends that orbit to a different one.  Such a
map exists iff two integers share an infinite parity skeleton, iff an infinite, co-infinite
sub-series of the orbit's own 2-adic expansion sums to an integer.  The agent believes there are no
solutions (~95%), which is not provable with current tools.

**`amusical_three_mul_sub_four`.**  Affine maps commute with `U` on at most one branch class
(agent's Theorem A).  Example: `3y − 4` commutes with `U` on `1 + 4ℤ`.

**`two_mul_not_orbit_map`.**  Multiplication by `2` does not map orbits to orbits: `22` and
`U⁻¹ 22 = 29` share an orbit, but `44` (on the 12-cycle) and `58` do not (agent's Proposition N).
-/

namespace CollatzMoonshot.Amusical

/-- **Proved.**  `y ↦ 3y − 4` commutes with `U` on the class `1 + 4ℤ`. -/
theorem amusical_three_mul_sub_four (m : ℤ) :
    amusical (3 * (4 * m + 1) - 4) = 3 * amusical (4 * m + 1) - 4 := by
  unfold amusical
  split_ifs <;> omega

/-- A period of `x` is a period of every point on its orbit. -/
theorem iterate_eq_of_mem_amusicalOrbit {x y : ℤ} {p : ℕ} (hx : amusical^[p] x = x)
    (hy : y ∈ amusicalOrbit x) : amusical^[p] y = y := by
  obtain ⟨j, rfl⟩ := hy
  have hp : (amusicalPerm ^ (p : ℤ)) x = x := by rw [amusicalPerm_pow_nat_apply]; exact hx
  rw [← amusicalPerm_pow_nat_apply, ← Equiv.Perm.mul_apply, ← zpow_add, add_comm, zpow_add,
    Equiv.Perm.mul_apply, hp]

/-- **Proved.**  `×2` does not map orbits to orbits: `U⁻¹ 22 = 29`, but `2 · 29 = 58` is not on
the orbit of `2 · 22 = 44`, the 12-cycle. -/
theorem two_mul_not_orbit_map : amusicalInv 22 = 29 ∧ (2 * 29 : ℤ) ∉ amusicalOrbit (2 * 22) := by
  refine ⟨by decide, fun h => ?_⟩
  have h44 : amusical^[12] (2 * 22 : ℤ) = 2 * 22 := by decide
  have h58 : amusical^[12] (2 * 29 : ℤ) ≠ 2 * 29 := by decide
  exact h58 (iterate_eq_of_mem_amusicalOrbit h44 h)

/-- **Reopen condition (wall).**  Two distinct integers whose orbits have the same parity
skeleton from some point on: `U^(a+j) y` and `U^(b+j) z` take the same branch (`stepSym`: even,
`1 mod 4`, `3 mod 4`) for every `j`, on different orbits.  By the agent's Proposition T this would supply the
partial multiplicative symmetry.  Believed to have no instances (~95%). -/
def AmusicalSharedSkeleton : Prop :=
  ∃ y z : ℤ, ∃ a b : ℕ, z ∉ amusicalOrbit y ∧
    ∀ j : ℕ, stepSym (amusical^[a + j] y) = stepSym (amusical^[b + j] z)

end CollatzMoonshot.Amusical
