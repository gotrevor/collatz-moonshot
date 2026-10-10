/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

namespace CollatzMoonshot.Benchmark.ArcOverlap

/-- The real-line part of a shared predecessor start.  A game start additionally lies in [0,1). -/
def SharedStart (l u v : ℝ) : Prop :=
  ∃ a : ℝ, a ≤ u ∧ u ≤ a + l / 3 ∧ a ≤ v ∧ v ≤ a + l / 3

/-- Goodness of two target bases must be strengthened to a distance estimate.
This equivalence does not enforce the arc or the [0,1) start restriction. -/
theorem sharedStart_iff (l u v : ℝ) (hl : 0 ≤ l) :
    SharedStart l u v ↔ |u - v| ≤ l / 3 := by
  constructor
  · rintro ⟨a, h1, h2, h3, h4⟩
    rw [abs_le]
    constructor <;> linarith
  · intro h
    obtain ⟨h1, h2⟩ := abs_le.mp h
    rcases le_total u v with huv | hvu
    · exact ⟨u, le_rfl, by linarith, huv, by linarith⟩
    · exact ⟨v, hvu, by linarith, le_rfl, by linarith⟩

/-- With equal parity and equal floor branch, the needed separation is l/2 in successor
fractional coordinates.  Different floor branches require comparing lifted coordinates. -/
theorem sharedStart_scaled_iff (l u v d : ℝ) (hl : 0 ≤ l) :
    SharedStart l u v ↔ |(3 * u / 2 + d) - (3 * v / 2 + d)| ≤ l / 2 := by
  rw [sharedStart_iff l u v hl]
  have e : (3 * u / 2 + d) - (3 * v / 2 + d) = (3 / 2 : ℝ) * (u - v) := by ring
  rw [e, abs_mul]
  norm_num
  constructor <;> intro h <;> linarith

/-- Local obstruction: both legal-choice start intervals can be nonempty and disjoint.
The choices u=1/6 and v=1/2 both fit width 2l/3 inside the arc [0,1], with l=1/4.
This is NOT a winning-strategy counterexample: global closure is deliberately absent. -/
theorem good_choices_need_not_share_start :
    (Set.Icc (1 / 12 : ℝ) (1 / 6)).Nonempty ∧
    (Set.Icc (5 / 12 : ℝ) (1 / 2)).Nonempty ∧
    (0 ≤ (1 / 6 : ℝ) ∧ (1 / 6 : ℝ) + 2 * (1 / 4) / 3 ≤ 1) ∧
    (0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) + 2 * (1 / 4) / 3 ≤ 1) ∧
    ¬ SharedStart (1 / 4) (1 / 6) (1 / 2) := by
  norm_num [sharedStart_iff, Set.nonempty_Icc]

/-- A possible contraction mechanism, conditional on legal matched inverse branches:
inverse scaling shrinks a gap by 2/3 and widening starts subtracts l/3.
Arc clipping can invalidate that recurrence; no clipping estimate is asserted here. -/
theorem inverse_gap_identity (l gap : ℝ) :
    (2 * gap / 3 - l / 3) + l = (2 / 3 : ℝ) * (gap + l) := by ring

end CollatzMoonshot.Benchmark.ArcOverlap
