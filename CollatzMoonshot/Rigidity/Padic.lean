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

/-!
## Regularity of `T2` (milestone M2 prerequisites)

Every transfer statement in this lane - Krylov-Bogolyubov above all - needs `T2`
continuous on the compact space `ℤ_[2]`.  Both halves are ultrametric facts: the
even set is the open unit ball, hence **clopen**, so the gluing frontier is empty
and no matching condition is owed; and halving is exactly `2`-Lipschitz there
because `‖2‖ = 1/2` scales every distance by two.
-/

/-- `‖2‖ = 1/2` in `ℤ_[2]`. -/
theorem norm_two_z2 : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
  simpa using PadicInt.norm_p (p := 2)

/-- The even set **is** the open unit ball: the arithmetic parity condition is a
metric condition upstairs.  That is why it is clopen. -/
theorem evenSet_eq_ball : {x : ℤ_[2] | (2 : ℤ_[2]) ∣ x} = Metric.ball 0 1 := by
  ext x
  simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
  exact_mod_cast (PadicInt.norm_lt_one_iff_dvd x).symm

/-- The even set is clopen, so `frontier {x | 2 ∣ x} = ∅` and the two branches of
`T2` never have to agree anywhere. -/
theorem isClopen_evenSet : IsClopen {x : ℤ_[2] | (2 : ℤ_[2]) ∣ x} := by
  rw [evenSet_eq_ball]
  exact IsUltrametricDist.isClopen_ball 0 1

/-- Halving **doubles** 2-adic distance. -/
theorem norm_half_sub {x y : ℤ_[2]} (hx : (2 : ℤ_[2]) ∣ x) (hy : (2 : ℤ_[2]) ∣ y) :
    ‖half x - half y‖ = 2 * ‖x - y‖ := by
  have h : (2 : ℤ_[2]) * (half x - half y) = x - y := by
    rw [mul_sub, two_mul_half hx, two_mul_half hy]
  have h' := congrArg norm h
  rw [norm_mul, norm_two_z2] at h'
  rw [← h']
  ring

theorem lipschitzOnWith_half :
    LipschitzOnWith 2 half {x : ℤ_[2] | (2 : ℤ_[2]) ∣ x} := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [dist_eq_norm, dist_eq_norm, norm_half_sub hx hy]
  norm_num

theorem continuousOn_half : ContinuousOn half {x : ℤ_[2] | (2 : ℤ_[2]) ∣ x} :=
  lipschitzOnWith_half.continuousOn

open scoped Classical in
/-- **`T2` is continuous.**  The prerequisite for Krylov-Bogolyubov transfer (M2):
a continuous self-map of the compact space `ℤ_[2]` admits invariant measures, and
every orbit-empirical limit is one of them. -/
theorem continuous_T2 : Continuous T2 := by
  unfold T2
  refine continuous_if ?_ ?_ ?_
  · intro a ha
    simp [isClopen_evenSet.frontier_eq] at ha
  · rw [isClopen_evenSet.isClosed.closure_eq]
    exact continuousOn_half
  · exact Continuous.continuousOn (by fun_prop)

/-! ## The negative 2-cycle: a live witness against unconditioned rigidity

`-1 = …1111` is a unit of `ℤ_[2]`, so `T2` sends it to `-2` and back.  One odd
step, one even step: **odd frequency 1/2**, well above the sharp drift threshold
`log 2 / log 6`.  This 2-cycle carries an invariant measure, so any parity
statement quantified over *all* `T2`-invariant measures is false.  Whatever the
lane keystone says, the arithmetic conditioning has to be load-bearing.
(Downstairs this is the `3n+1` cycle on the negative integers.) -/

theorem not_two_dvd_neg_one : ¬ (2 : ℤ_[2]) ∣ (-1) := by
  intro h
  have h1 : (2 : ℤ_[2]) ∣ 1 := dvd_neg.mp h
  exact (PadicInt.prime_p (p := 2)).not_unit (isUnit_of_dvd_one h1)

theorem T2_neg_one : T2 (-1) = -2 := by
  unfold T2
  rw [if_neg not_two_dvd_neg_one]
  ring

theorem T2_neg_two : T2 (-2) = -1 := by
  have hdvd : (2 : ℤ_[2]) ∣ (-2) := ⟨-1, by ring⟩
  unfold T2
  rw [if_pos hdvd]
  exact half_eq (by ring)

/-- The negative 2-cycle, closed. -/
theorem T2_neg_cycle : T2 (T2 (-1)) = -1 := by rw [T2_neg_one, T2_neg_two]


end CollatzMoonshot
