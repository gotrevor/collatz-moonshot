/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Benchmark.ArcTrap

namespace CollatzMoonshot.Benchmark.ArcFattening

/-- Real-coordinate version of the two-child game.  The finite-memory interpretation uses
a set periodic with period 2^k and child displacement h = 2^(k-1).  Equivalence with
ArcTrap.KRelaxedStrategy, including normalization across integers, is not proved here. -/
def LiftedStrategy (s t l h : ℝ) (P : Set ℝ) : Prop :=
  0 < l ∧ ∀ x ∈ P, ∃ v : ℝ, x ≤ v ∧ v + 2 * l / 3 ≤ x + l ∧
    (∃ j : ℤ, (j : ℝ) + s ≤ v ∧ v + 2 * l / 3 ≤ j + s + t) ∧
    ∀ b : ℕ, b < 2 → 3 * v / 2 + b * h ∈ P

/-- Increase window width by e, shift centers accordingly, and allow a start interval
of radius e/6 around each shifted old start. -/
def fatten (e : ℝ) (P : Set ℝ) : Set ℝ :=
  {y | ∃ x ∈ P, ∃ z : ℝ, |z| ≤ e / 6 ∧ y = x - e / 2 + z}

/-- Widening the arc by e/3 at each end makes every real-coordinate strategy robust.
The selected move v-e/3 lands exactly at the center of each fattened successor fiber.
This changes the parameters; it does not establish liveness at the original arc. -/
theorem LiftedStrategy.fatten {s t l h e : ℝ} {P : Set ℝ}
    (hP : LiftedStrategy s t l h P) (he : 0 ≤ e) :
    LiftedStrategy (s - e / 3) (t + 2 * e / 3) (l + e) h (fatten e P) := by
  refine ⟨by linarith [hP.1], ?_⟩
  rintro y ⟨x, hx, z, hz, rfl⟩
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  obtain ⟨v, hv1, hv2, ⟨j, hj1, hj2⟩, hv⟩ := hP.2 x hx
  refine ⟨v - e / 3, by linarith, by linarith,
    ⟨j, by linarith, by linarith⟩, ?_⟩
  intro b hb
  exact ⟨3 * v / 2 + b * h, hv b hb, 0, by simp; positivity, by ring⟩

/-- A live fattened strategy has an interval of starts whenever e>0. -/
theorem fatten_contains_interval {e x : ℝ} {P : Set ℝ} (hx : x ∈ P) :
    Set.Icc (x - 2 * e / 3) (x - e / 3) ⊆ fatten e P := by
  intro y hy
  refine ⟨x, hx, y - x + e / 2, ?_, by ring⟩
  rw [abs_le]
  constructor <;> linarith [hy.1, hy.2]

/-- Fattening preserves translation invariance, so the period required by a finite-memory
encoding is not lost.  The separate encoding equivalence is still needed. -/
theorem fatten_translation {e M : ℝ} {P : Set ℝ}
    (hP : ∀ x ∈ P, x + M ∈ P) :
    ∀ y ∈ fatten e P, y + M ∈ fatten e P := by
  rintro y ⟨x, hx, z, hz, rfl⟩
  exact ⟨x + M, hP x hx, z, hz, by ring⟩

/-- A smaller fattening whose starts and successor landings admit uniform move margins. -/
def fattenCore (e : ℝ) (P : Set ℝ) : Set ℝ :=
  {y | ∃ x ∈ P, ∃ z : ℝ, |z| ≤ e / 12 ∧ y = x - e / 2 + z}

/-- Robust interface for a future rounded-solver inclusion proof.  Every core start has
an entire interval of legal moves of radius e/24.  Each child is within e/16 of a core
center, leaving e/48 before the core boundary at radius e/12.  For e>0 these margins
are strictly positive.  Neither residue encoding nor lattice rounding is asserted here. -/
theorem LiftedStrategy.robust_fatten {s t l h e : ℝ} {P : Set ℝ}
    (hP : LiftedStrategy s t l h P) (he : 0 ≤ e) :
    ∀ y ∈ fattenCore e P, ∃ v : ℝ, ∀ q : ℝ, |q| ≤ e / 24 →
      y ≤ v + q ∧ v + q + 2 * (l + e) / 3 ≤ y + (l + e) ∧
      (∃ j : ℤ, (j : ℝ) + (s - e / 2) ≤ v + q ∧
        v + q + 2 * (l + e) / 3 ≤ j + (s - e / 2) + (t + e)) ∧
      ∀ b : ℕ, b < 2 → ∃ x ∈ P,
        |3 * (v + q) / 2 + b * h - (x - e / 2)| ≤ e / 16 := by
  rintro y ⟨x, hx, z, hz, rfl⟩
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  obtain ⟨v, hv1, hv2, ⟨j, hj1, hj2⟩, hv⟩ := hP.2 x hx
  refine ⟨v - e / 3, ?_⟩
  intro q hq
  obtain ⟨hq1, hq2⟩ := abs_le.mp hq
  refine ⟨by linarith, by linarith, ⟨j, by linarith, by linarith⟩, ?_⟩
  intro b hb
  refine ⟨3 * v / 2 + b * h, hv b hb, ?_⟩
  rw [abs_le]
  constructor <;> linarith

/-- In particular, the core itself is a strategy on the widened arc. -/
theorem LiftedStrategy.fattenCore {s t l h e : ℝ} {P : Set ℝ}
    (hP : LiftedStrategy s t l h P) (he : 0 ≤ e) :
    LiftedStrategy (s - e / 2) (t + e) (l + e) h (fattenCore e P) := by
  refine ⟨by linarith [hP.1], ?_⟩
  intro y hy
  obtain ⟨v, hv⟩ := hP.robust_fatten he y hy
  obtain ⟨hv1, hv2, hj, hb⟩ := hv 0 (by simp; positivity)
  simp only [add_zero] at hv1 hv2 hj hb
  refine ⟨v, hv1, hv2, hj, ?_⟩
  intro b hb'
  obtain ⟨x, hx, hdist⟩ := hb b hb'
  exact ⟨x, hx, 3 * v / 2 + b * h - (x - e / 2), by linarith, by ring⟩

/-- Read the integer residue of a physical start using Euclidean remainder, also for
negative starts. -/
noncomputable def residue (k : ℕ) (x : ℝ) : ℕ := (⌊x⌋ % (2 ^ k : ℤ)).toNat

/-- Periodic real-coordinate realization of a family of fractional start sets. -/
def physicalize (k : ℕ) (P : ℕ → Set ℝ) : Set ℝ :=
  {x | Int.fract x ∈ P (residue k x)}

/-- Project a physical strategy to integer residues and fractional starts. -/
def residualize (k : ℕ) (P : Set ℝ) (r : ℕ) : Set ℝ :=
  {a | ∃ x ∈ P, residue k x = r ∧ Int.fract x = a}

/-- Open bridge, reviewed by Opus on 2026-10-10; confidence 92%, not a theorem.
The key arithmetic is that replacing m by m+2^k*q adds 3*2^(k-1)*q to floor(3m/2),
so the two children are permuted modulo 2^k.  k>=1 is essential. -/
def KToLiftedBridge : Prop :=
  ∀ (s t l : ℝ) (k : ℕ) (P : ℕ → Set ℝ), 1 ≤ k →
    ArcTrap.KRelaxedStrategy s t l k P →
    LiftedStrategy s t l (2 ^ (k - 1)) (physicalize k P)

/-- Open converse bridge; confidence 92%, not a theorem.  No periodicity assumption
is proposed: each physical witness supplies a move and both projected children. -/
def LiftedToKBridge : Prop :=
  ∀ (s t l : ℝ) (k : ℕ) (P : Set ℝ), 1 ≤ k →
    LiftedStrategy s t l (2 ^ (k - 1)) P →
    ArcTrap.KRelaxedStrategy s t l k (residualize k P)

end CollatzMoonshot.Benchmark.ArcFattening
