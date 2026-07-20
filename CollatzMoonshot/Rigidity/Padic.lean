/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.Basic

/-!
# The 2-adic extension of the Collatz map

The Collatz map extends to `ℤ_[2]`: parity is a clopen condition (divisibility by
`2`), halving is exact division on the even part, and `3x + 1` is polynomial.  The
payoff of this file is `T2_natCast`, the **base intertwining**: the ℕ-dynamics is
the restriction of the ℤ₂-dynamics along the canonical embedding.  Trivial-looking
and load-bearing - it is the floor of the conjugacy layer (Bernstein-Lagarias) and
of every measure-level statement in this lane.  The *open* intertwining (upgrading
`T2`-invariance to genuine ×2,×3 structure) is the lane's keystone and lives as a
working conjecture in `Rigidity/Invariant.lean`, not here.
-/

namespace CollatzMoonshot

open scoped Classical in
/-- Exact division by `2` on `ℤ_[2]` (junk value `0` on non-divisible inputs). -/
noncomputable def half (x : ℤ_[2]) : ℤ_[2] :=
  if h : (2 : ℤ_[2]) ∣ x then h.choose else 0

theorem two_ne_zero_z2 : (2 : ℤ_[2]) ≠ 0 := by
  have h : ((2 : ℕ) : ℤ_[2]) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
  exact_mod_cast h

theorem two_mul_half {x : ℤ_[2]} (h : (2 : ℤ_[2]) ∣ x) : 2 * half x = x := by
  rw [half, dif_pos h]
  exact h.choose_spec.symm

theorem half_eq {x y : ℤ_[2]} (h : x = 2 * y) : half x = y := by
  have h2 : (2 : ℤ_[2]) * half x = 2 * y := by rw [two_mul_half ⟨y, h⟩, h]
  exact mul_left_cancel₀ two_ne_zero_z2 h2

/-- Parity transfers through the embedding: `2 ∣ n` in `ℤ_[2]` iff `2 ∣ n` in `ℕ`.
The forward direction is where `ℤ_[2]` earns its keep: `2` is prime (not a unit)
there, so it cannot divide `1`. -/
theorem two_dvd_natCast_iff (n : ℕ) : (2 : ℤ_[2]) ∣ (n : ℤ_[2]) ↔ 2 ∣ n := by
  constructor
  · intro h
    by_contra hodd
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [hk] at h
    push_cast at h
    have h1 : (2 : ℤ_[2]) ∣ 1 := (dvd_add_right ⟨(k : ℤ_[2]), rfl⟩).mp h
    exact (PadicInt.prime_p (p := 2)).not_unit (isUnit_of_dvd_one h1)
  · rintro ⟨k, hk⟩
    exact ⟨(k : ℤ_[2]), by rw [hk]; push_cast; ring⟩

theorem half_natCast {n : ℕ} (h : 2 ∣ n) : half (n : ℤ_[2]) = ((n / 2 : ℕ) : ℤ_[2]) := by
  apply half_eq
  obtain ⟨k, hk⟩ := h
  subst hk
  rw [Nat.mul_div_cancel_left k (by norm_num)]
  push_cast
  ring

open scoped Classical in
/-- The Collatz map extended to the 2-adic integers: halve on the even clopen set,
`3x + 1` off it.  Mirrors `step` exactly (un-accelerated). -/
noncomputable def T2 (x : ℤ_[2]) : ℤ_[2] :=
  if (2 : ℤ_[2]) ∣ x then half x else 3 * x + 1

/-- **The base intertwining**: `T2` extends `step` through the canonical embedding
`ℕ → ℤ_[2]`.  Every orbit fact downstairs is a fact about the compact dynamics
upstairs. -/
theorem T2_natCast (n : ℕ) : T2 (n : ℤ_[2]) = ((step n : ℕ) : ℤ_[2]) := by
  unfold T2 step
  by_cases h : 2 ∣ n
  · rw [if_pos ((two_dvd_natCast_iff n).mpr h), if_pos (by omega : n % 2 = 0),
      half_natCast h]
  · rw [if_neg (fun hc => h ((two_dvd_natCast_iff n).mp hc)),
      if_neg (by omega : ¬n % 2 = 0)]
    push_cast
    ring

/-- The trivial cycle survives upstairs. -/
theorem T2_one : T2 1 = 4 := by simpa using T2_natCast 1

theorem T2_four : T2 4 = 2 := by simpa using T2_natCast 4

theorem T2_two : T2 2 = 1 := by simpa using T2_natCast 2

end CollatzMoonshot
