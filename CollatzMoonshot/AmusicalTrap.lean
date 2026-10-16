/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Amusical

/-!
# Residue traps: a one-swap neighbour of `U` with infinitely many orbits (research §55)

A permutation `σ` of `ℤ` that maps a set `C` into itself has a *trap*: an orbit enters `C` at most
once, at a point of `C ∖ σ(C)`, and never leaves.  So distinct entry points lie on distinct
orbits, and each such orbit is infinite.

* `infinitelyManyInfiniteOrbits_of_trap`: infinitely many nonnegative entry points give
  infinitely many infinite orbits.
* **Theorem V.**  `amusicalV` is `U` with the targets of `0 (mod 2)` and `3 (mod 8)` swapped:
  `2k ↦ 6k + 2`, `8k + 3 ↦ 3k`, and `U` elsewhere.  The evens are a trap with entry points
  `≡ 0, 4 (mod 6)`, so `V` has infinitely many infinite orbits: Klamkin's conclusion for a one-swap
  neighbour of `U`.  `U` itself has no residue trap (every branch is onto `ℤ₂`).
* **Avoidance.**  Every infinite orbit of `U` visits `{0, 3, 5} (mod 8)` infinitely often going
  forward.
* **Sign-blind Collatz gate.**  For odd `x ↦ (3x ± 1)/2` with the sign chosen per point, some
  choice agreeing with Collatz below any bound `K` has a divergent orbit, so an argument blind to
  the sign cannot prove the Collatz conjecture.
-/

namespace CollatzMoonshot.AmusicalTrap

open CollatzMoonshot.Amusical

/-! ## The trap theorem -/

/-- The two-sided orbit `{σ^j x : j ∈ ℤ}` of `x`. -/
def permOrbit (σ : Equiv.Perm ℤ) (x : ℤ) : Set ℤ :=
  Set.range fun j : ℤ => (σ ^ j) x

/-- Infinitely many infinite orbits of `σ` meet the nonnegative integers. -/
def InfinitelyManyInfiniteOrbits (σ : Equiv.Perm ℤ) : Prop :=
  {O : Set ℤ | ∃ x : ℤ, 0 ≤ x ∧ O = permOrbit σ x ∧ O.Infinite}.Infinite

/-- **Open.**  If `σ` maps `C` into itself, distinct entry points (points of `C ∖ σ(C)`) lie on
distinct orbits. -/
theorem permOrbit_injOn_entry (σ : Equiv.Perm ℤ) {C : Set ℤ} (hC : ∀ x ∈ C, σ x ∈ C) :
    Set.InjOn (permOrbit σ) (C \ σ '' C) := by
  sorry

/-- **Open.**  The orbit through an entry point of a trap is infinite. -/
theorem permOrbit_infinite_of_entry (σ : Equiv.Perm ℤ) {C : Set ℤ} (hC : ∀ x ∈ C, σ x ∈ C)
    {x : ℤ} (hx : x ∈ C \ σ '' C) : (permOrbit σ x).Infinite := by
  sorry

/-- **Open (trap theorem).**  Infinitely many nonnegative entry points of a trap give infinitely
many infinite orbits. -/
theorem infinitelyManyInfiniteOrbits_of_trap (σ : Equiv.Perm ℤ) {C : Set ℤ}
    (hC : ∀ x ∈ C, σ x ∈ C) (hE : {x : ℤ | 0 ≤ x ∧ x ∈ C \ σ '' C}.Infinite) :
    InfinitelyManyInfiniteOrbits σ := by
  sorry

/-! ## Theorem V -/

/-- `U` with the targets of `0 (mod 2)` and `3 (mod 8)` swapped: `2k ↦ 6k + 2`, `4k + 1 ↦ 3k + 1`,
`8k + 3 ↦ 3k`, `8k + 7 ↦ 6k + 5`. -/
def amusicalV (n : ℤ) : ℤ :=
  if n % 2 = 0 then 3 * n + 2
  else if n % 4 = 1 then 3 * (n / 4) + 1
  else if n % 8 = 3 then 3 * (n / 8)
  else 6 * (n / 8) + 5

/-- The inverse of `amusicalV`: `3m ↦ 8m + 3`, `3m + 1 ↦ 4m + 1`, `6m + 2 ↦ 2m`,
`6m + 5 ↦ 8m + 7`. -/
def amusicalVInv (m : ℤ) : ℤ :=
  if m % 3 = 0 then 8 * (m / 3) + 3
  else if m % 3 = 1 then 4 * (m / 3) + 1
  else if m % 6 = 2 then (m - 2) / 3
  else 8 * (m / 6) + 7

/-- **Open.** -/
theorem amusicalVInv_amusicalV (n : ℤ) : amusicalVInv (amusicalV n) = n := by
  sorry

/-- **Open.** -/
theorem amusicalV_amusicalVInv (m : ℤ) : amusicalV (amusicalVInv m) = m := by
  sorry

/-- `amusicalV` as a permutation of `ℤ`. -/
def amusicalVPerm : Equiv.Perm ℤ where
  toFun := amusicalV
  invFun := amusicalVInv
  left_inv := amusicalVInv_amusicalV
  right_inv := amusicalV_amusicalVInv

/-- **Open.**  `V` agrees with `U` off the two swapped classes `0 (mod 2)` and `3 (mod 8)`. -/
theorem amusicalV_eq_amusical {n : ℤ} (h : n % 4 = 1 ∨ n % 8 = 7) :
    amusicalV n = amusical n := by
  sorry

/-- **Open.**  The evens are a trap for `V`. -/
theorem amusicalV_even_trap : ∀ x ∈ {x : ℤ | x % 2 = 0}, amusicalVPerm x ∈ {x : ℤ | x % 2 = 0} := by
  sorry

/-- **Open.**  The entry points of the even trap are the classes `0, 4 (mod 6)`. -/
theorem amusicalV_entry_iff (x : ℤ) :
    x ∈ {x : ℤ | x % 2 = 0} \ amusicalVPerm '' {x : ℤ | x % 2 = 0} ↔ x % 6 = 0 ∨ x % 6 = 4 := by
  sorry

/-- **Open (Theorem V).**  `V` has infinitely many infinite orbits. -/
theorem amusicalV_infinitelyManyInfiniteOrbits : InfinitelyManyInfiniteOrbits amusicalVPerm := by
  sorry

/-! ## Avoidance for `U` -/

/-- **Open.**  Every infinite orbit of `U` visits `{0, 3, 5} (mod 8)` infinitely often going
forward. -/
theorem amusical_visits_zero_three_five {x : ℤ} (hx : (amusicalOrbit x).Infinite) (k₀ : ℕ) :
    ∃ k ≥ k₀, amusical^[k] x % 8 = 0 ∨ amusical^[k] x % 8 = 3 ∨ amusical^[k] x % 8 = 5 := by
  sorry

/-! ## Sign-blind Collatz gate -/

/-- A sign-choice Collatz map: even `x ↦ x / 2`; odd `x ↦ (3x + 1)/2` where `ε x`, else
`(3x − 1)/2`.  `ε = fun _ ↦ true` is the Collatz map. -/
def signCollatz (ε : ℕ → Bool) (x : ℕ) : ℕ :=
  if x % 2 = 0 then x / 2 else if ε x then (3 * x + 1) / 2 else (3 * x - 1) / 2

/-- **Open (sign-blind gate).**  For every bound `K` some sign choice agrees with Collatz below
`K` and has a divergent orbit. -/
theorem signBlind_gate (K : ℕ) :
    ∃ ε : ℕ → Bool, (∀ x < K, ε x = true) ∧
      ∃ x : ℕ, Filter.Tendsto (fun k => (signCollatz ε)^[k] x) Filter.atTop Filter.atTop := by
  sorry

/-- **Open.**  The all-minus member (the `3x − 1` map) has the cycle `5 → 7 → 10 → 5`. -/
theorem signCollatz_minus_cycle : (signCollatz fun _ => false)^[3] 5 = 5 := by
  sorry

end CollatzMoonshot.AmusicalTrap
