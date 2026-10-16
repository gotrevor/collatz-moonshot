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

/-- Forward invariance of a trap under natural powers. -/
theorem perm_pow_mem (σ : Equiv.Perm ℤ) {C : Set ℤ} (hC : ∀ x ∈ C, σ x ∈ C) {x : ℤ}
    (hx : x ∈ C) (n : ℕ) : (σ ^ n) x ∈ C := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hC _ ih

/-- A positive power of `σ` applied to a point of a trap lands in `σ(C)`. -/
theorem perm_pow_succ_mem_image (σ : Equiv.Perm ℤ) {C : Set ℤ} (hC : ∀ x ∈ C, σ x ∈ C)
    {x : ℤ} (hx : x ∈ C) (n : ℕ) : (σ ^ (n + 1)) x ∈ σ '' C := by
  rw [pow_succ', Equiv.Perm.mul_apply]
  exact ⟨_, perm_pow_mem σ hC hx n, rfl⟩

/-- If a natural power of `σ` carries a point of `C` to an entry point, the power is trivial. -/
theorem perm_pow_eq_entry (σ : Equiv.Perm ℤ) {C : Set ℤ} (hC : ∀ x ∈ C, σ x ∈ C) {x y : ℤ}
    (hx : x ∈ C) (hy : y ∉ σ '' C) (n : ℕ) (h : (σ ^ n) x = y) : y = x := by
  cases n with
  | zero => simpa using h.symm
  | succ n => exact absurd (h ▸ perm_pow_succ_mem_image σ hC hx n) hy

/-- **Proved.**  If `σ` maps `C` into itself, distinct entry points (points of `C ∖ σ(C)`) lie on
distinct orbits.  Paper proof: `y = σ^j x`; a positive power puts `y` (or `x`) in `σ(C)`. -/
theorem permOrbit_injOn_entry (σ : Equiv.Perm ℤ) {C : Set ℤ} (hC : ∀ x ∈ C, σ x ∈ C) :
    Set.InjOn (permOrbit σ) (C \ σ '' C) := by
  intro x hx y hy hxy
  have hymem : y ∈ permOrbit σ x := hxy ▸ ⟨0, by simp⟩
  obtain ⟨j, hj⟩ := hymem
  dsimp only at hj
  rcases Int.eq_nat_or_neg j with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast] at hj
    exact (perm_pow_eq_entry σ hC hx.1 hy.2 n hj).symm
  · have hxj : (σ ^ n) y = x := by
      rw [← hj, zpow_neg, zpow_natCast]; exact Equiv.apply_symm_apply _ _
    exact perm_pow_eq_entry σ hC hy.1 hx.2 n hxj

/-- **Proved.**  The orbit through an entry point of a trap is infinite.  Paper proof: a finite
orbit makes `x` periodic, `x = σ^(p+1) x ∈ σ(C)`. -/
theorem permOrbit_infinite_of_entry (σ : Equiv.Perm ℤ) {C : Set ℤ} (hC : ∀ x ∈ C, σ x ∈ C)
    {x : ℤ} (hx : x ∈ C \ σ '' C) : (permOrbit σ x).Infinite := by
  intro hfin
  obtain ⟨m, n, hmn, heq⟩ := hfin.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ => (σ ^ n) x)
    (fun n => show (σ ^ n) x ∈ permOrbit σ x from ⟨(n : ℤ), by simp⟩)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
  have hper : (σ ^ (d + 1)) x = x := by
    apply (σ ^ m).injective
    change (σ ^ m) x = (σ ^ (m + d + 1)) x at heq
    rw [← Equiv.Perm.mul_apply, ← pow_add, show m + (d + 1) = m + d + 1 by omega]
    exact heq.symm
  exact hx.2 (hper ▸ perm_pow_succ_mem_image σ hC hx.1 d)

/-- **Proved (trap theorem).**  Infinitely many nonnegative entry points of a trap give
infinitely many infinite orbits. -/
theorem infinitelyManyInfiniteOrbits_of_trap (σ : Equiv.Perm ℤ) {C : Set ℤ}
    (hC : ∀ x ∈ C, σ x ∈ C) (hE : {x : ℤ | 0 ≤ x ∧ x ∈ C \ σ '' C}.Infinite) :
    InfinitelyManyInfiniteOrbits σ := by
  have hinj : Set.InjOn (permOrbit σ) {x : ℤ | 0 ≤ x ∧ x ∈ C \ σ '' C} :=
    (permOrbit_injOn_entry σ hC).mono fun _ hx => hx.2
  refine (hE.image hinj).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx.1, rfl, permOrbit_infinite_of_entry σ hC hx.2⟩

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

/-- **Proved.** -/
theorem amusicalVInv_amusicalV (n : ℤ) : amusicalVInv (amusicalV n) = n := by
  unfold amusicalV amusicalVInv; split_ifs <;> omega

/-- **Proved.** -/
theorem amusicalV_amusicalVInv (m : ℤ) : amusicalV (amusicalVInv m) = m := by
  unfold amusicalV amusicalVInv; split_ifs <;> omega

/-- `amusicalV` as a permutation of `ℤ`. -/
def amusicalVPerm : Equiv.Perm ℤ where
  toFun := amusicalV
  invFun := amusicalVInv
  left_inv := amusicalVInv_amusicalV
  right_inv := amusicalV_amusicalVInv

/-- **Proved.**  `V` agrees with `U` off the two swapped classes `0 (mod 2)` and `3 (mod 8)`. -/
theorem amusicalV_eq_amusical {n : ℤ} (h : n % 4 = 1 ∨ n % 8 = 7) :
    amusicalV n = amusical n := by
  unfold amusicalV amusical; split_ifs <;> omega

/-- **Proved.**  The evens are a trap for `V`. -/
theorem amusicalV_even_trap : ∀ x ∈ {x : ℤ | x % 2 = 0}, amusicalVPerm x ∈ {x : ℤ | x % 2 = 0} := by
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  change amusicalV x % 2 = 0
  unfold amusicalV; split_ifs <;> omega

/-- **Proved.**  The entry points of the even trap are the classes `0, 4 (mod 6)`.  Paper proof:
`V(2e) = 6e + 2`. -/
theorem amusicalV_entry_iff (x : ℤ) :
    x ∈ {x : ℤ | x % 2 = 0} \ amusicalVPerm '' {x : ℤ | x % 2 = 0} ↔ x % 6 = 0 ∨ x % 6 = 4 := by
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hx, hnot⟩
    by_contra h
    apply hnot
    refine ⟨(x - 2) / 3, by omega, ?_⟩
    change amusicalV ((x - 2) / 3) = x
    unfold amusicalV; split_ifs <;> omega
  · intro h
    refine ⟨by omega, ?_⟩
    rintro ⟨y, hy, hyx⟩
    change amusicalV y = x at hyx
    unfold amusicalV at hyx; split_ifs at hyx <;> omega

/-- **Proved (Theorem V).**  `V` has infinitely many infinite orbits.  Paper proof: the trap
theorem with `C` the evens, whose nonnegative entry points include every `6n`. -/
theorem amusicalV_infinitelyManyInfiniteOrbits : InfinitelyManyInfiniteOrbits amusicalVPerm := by
  apply infinitelyManyInfiniteOrbits_of_trap amusicalVPerm amusicalV_even_trap
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 6 * (n : ℤ)) ?_ ?_
  · intro a b hab
    simp only at hab
    omega
  · intro n
    refine ⟨by positivity, (amusicalV_entry_iff _).2 (Or.inl ?_)⟩
    omega

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

/-- **Proved (sign-blind gate).**  For every bound `K` some sign choice agrees with Collatz below
`K` and has a divergent orbit.  Paper proof: `ε y := y < K ∨ y % 4 = 3`; from `4K + 3` every
iterate is odd and the next one is larger. -/
theorem signBlind_gate (K : ℕ) :
    ∃ ε : ℕ → Bool, (∀ x < K, ε x = true) ∧
      ∃ x : ℕ, Filter.Tendsto (fun k => (signCollatz ε)^[k] x) Filter.atTop Filter.atTop := by
  let ε : ℕ → Bool := fun y => decide (y < K ∨ y % 4 = 3)
  refine ⟨ε, fun x hx => by simp [ε, hx], 4 * K + 3, ?_⟩
  have hinv : ∀ k : ℕ, (signCollatz ε)^[k] (4 * K + 3) % 2 = 1 ∧
      4 * K + 3 + k ≤ (signCollatz ε)^[k] (4 * K + 3) := by
    intro k
    induction k with
    | zero => simp; omega
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      set y := (signCollatz ε)^[k] (4 * K + 3)
      obtain ⟨hodd, hge⟩ := ih
      unfold signCollatz
      rw [if_neg (by omega)]
      by_cases h3 : y % 4 = 3
      · rw [if_pos (by simp [ε, h3])]
        omega
      · rw [if_neg (by simp [ε]; omega)]
        omega
  refine Filter.tendsto_atTop_mono (fun k => ?_) Filter.tendsto_id
  have := (hinv k).2
  simp only [id]
  omega

/-- **Proved.**  The all-minus member (the `3x − 1` map) has the cycle `5 → 7 → 10 → 5`. -/
theorem signCollatz_minus_cycle : (signCollatz fun _ => false)^[3] 5 = 5 := by
  decide

end CollatzMoonshot.AmusicalTrap
