/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjecture

/-!
# The backward formulation of `3x+1`: the smallest affine-closed set containing `1`

Lagarias (arXiv:2111.02635v1): the `3x+1` problem is the question of whether the smallest set
`S₀` of integers containing `1` and closed under the affine maps `x ↦ 2x` and `3x+2 ↦ 2x+1` is
the set of all positive integers.  This links `3x+1` to the Isard-Zwicky and Klarner-Rado
problems on sets closed under affine maps.

`BackwardSet` is `S₀`.  It is stated on `ℕ` because every element is positive
(`one_le_of_backwardSet`), so the integer and natural-number versions are the same set.
`backwardSet_iff_reachesOne` identifies it with the set of starts that reach `1`, and
`conjecture_iff_backwardSet_eq` is the equivalence with `Conjecture`.
-/

namespace CollatzMoonshot

/-- Lagarias's `S₀`: the smallest set containing `1` and closed under `x ↦ 2x` and
`3x+2 ↦ 2x+1`. -/
inductive BackwardSet : ℕ → Prop
  | one : BackwardSet 1
  | double {x : ℕ} : BackwardSet x → BackwardSet (2 * x)
  | branch {x : ℕ} : BackwardSet (3 * x + 2) → BackwardSet (2 * x + 1)

theorem step_two_mul (y : ℕ) : step (2 * y) = y := by
  unfold step; split_ifs <;> omega

theorem step_two_mul_add_one (y : ℕ) : step (2 * y + 1) = 6 * y + 4 := by
  unfold step; split_ifs <;> omega

theorem step_six_mul_add_four (y : ℕ) : step (6 * y + 4) = 3 * y + 2 := by
  unfold step; split_ifs <;> omega

theorem one_le_of_backwardSet {n : ℕ} (h : BackwardSet n) : 1 ≤ n := by
  induction h <;> omega

theorem reachesOne_of_backwardSet {n : ℕ} (h : BackwardSet n) : ReachesOne n := by
  induction h with
  | one => exact reachesOne_one
  | double _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, by rw [Function.iterate_succ_apply, step_two_mul]; exact hk⟩
  | branch _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 2, ?_⟩
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, step_two_mul_add_one,
      step_six_mul_add_four]
    exact hk

theorem backwardSet_of_iterate_eq_one (k : ℕ) :
    ∀ n : ℕ, step^[k] n = 1 → BackwardSet n := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk
    by_cases h1 : n = 1
    · subst h1; exact BackwardSet.one
    rcases Nat.even_or_odd' n with ⟨y, rfl | rfl⟩
    · cases k with
      | zero => exact absurd hk h1
      | succ k =>
        rw [Function.iterate_succ_apply, step_two_mul] at hk
        exact BackwardSet.double (ih k (by omega) y hk)
    · cases k with
      | zero => exact absurd hk h1
      | succ k =>
        cases k with
        | zero =>
          rw [Function.iterate_one, step_two_mul_add_one] at hk
          omega
        | succ k =>
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, step_two_mul_add_one,
            step_six_mul_add_four] at hk
          exact BackwardSet.branch (ih k (by omega) _ hk)

/-- `S₀` is exactly the set of starts whose `3x+1` orbit reaches `1`. -/
theorem backwardSet_iff_reachesOne (n : ℕ) : BackwardSet n ↔ ReachesOne n :=
  ⟨reachesOne_of_backwardSet, fun ⟨k, hk⟩ => backwardSet_of_iterate_eq_one k n hk⟩

/-- **The backward formulation.**  The `3x+1` conjecture holds iff `S₀` is the set of all
positive integers. -/
theorem conjecture_iff_backwardSet_eq :
    Conjecture ↔ {n : ℕ | BackwardSet n} = {n : ℕ | 1 ≤ n} := by
  constructor
  · intro hc
    ext n
    exact ⟨one_le_of_backwardSet, fun hn => (backwardSet_iff_reachesOne n).2 (hc n hn)⟩
  · intro heq n hn
    have : n ∈ {n : ℕ | BackwardSet n} := by rw [heq]; exact hn
    exact (backwardSet_iff_reachesOne n).1 this

end CollatzMoonshot
