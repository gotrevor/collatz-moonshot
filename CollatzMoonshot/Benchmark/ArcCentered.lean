/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Benchmark.ArcFattening

namespace CollatzMoonshot.Benchmark.ArcCentered

open ArcFattening

/-- Express candidate windows by their centres.  Width controls the allowed displacement
and erodes the arc band, but disappears from the successor map. -/
def CenteredStrategy (s t l h : ℝ) (C : Set ℝ) : Prop :=
  0 < l ∧ ∀ y ∈ C, ∃ z : ℝ, |z - y| ≤ l / 6 ∧
    (∃ j : ℤ, (j : ℝ) + s + l / 3 ≤ z ∧ z ≤ j + s + t - l / 3) ∧
    ∀ b : ℕ, b < 2 → 3 * z / 2 + b * h ∈ C

/-- The exact centre-coordinate formulation.  This is a change of variables, not a
memory-reduction theorem: h is unchanged in both directions. -/
theorem lifted_iff_centered (s t l h : ℝ) (P : Set ℝ) :
    LiftedStrategy s t l h P ↔
      CenteredStrategy s t l h ((fun x => x + l / 2) '' P) := by
  constructor
  · rintro ⟨hl, hP⟩
    refine ⟨hl, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨v, hv1, hv2, ⟨j, hj1, hj2⟩, hv⟩ := hP x hx
    refine ⟨v + l / 3, ?_, ⟨j, by linarith, by linarith⟩, ?_⟩
    · rw [abs_le]; constructor <;> linarith
    · intro b hb
      exact ⟨3 * v / 2 + b * h, hv b hb, by ring⟩
  · rintro ⟨hl, hC⟩
    refine ⟨hl, ?_⟩
    intro x hx
    obtain ⟨z, hz, ⟨j, hj1, hj2⟩, hzC⟩ := hC (x + l / 2) ⟨x, hx, rfl⟩
    obtain ⟨hz1, hz2⟩ := abs_le.mp hz
    refine ⟨z - l / 3, by linarith, by linarith,
      ⟨j, by linarith, by linarith⟩, ?_⟩
    intro b hb
    obtain ⟨w, hw, he⟩ := hzC b hb
    have he' : 3 * (z - l / 3) / 2 + b * h = w := by linarith
    rw [he']; exact hw

/-- On [beta,1-beta], legal kept-window centres lie around the half-integers.
This isolates precisely where reflection symmetry enters the game. -/
theorem symmetric_band_iff (β l z : ℝ) (j : ℤ) :
    ((j : ℝ) + β + l / 3 ≤ z ∧ z ≤ j + β + (1 - 2 * β) - l / 3) ↔
      |z - ((j : ℝ) + 1 / 2)| ≤ (1 - 2 * β) / 2 - l / 3 := by
  rw [abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Increasing the window width trades twice as much legal-band radius for displacement
radius.  A period-halving argument must respect this constraint. -/
theorem radius_tradeoff (t l : ℝ) : (t / 2 - l / 3) + 2 * (l / 6) = t / 2 := by ring

end CollatzMoonshot.Benchmark.ArcCentered
