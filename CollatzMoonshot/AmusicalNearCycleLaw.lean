/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycle

/-!
# Near-cycles: the equation, finiteness per return time, and the survivor count

The 2026-10-14 "ncnull" agent (research §37).  A `D`-near-cycle start `p` (`NearCycleStart`,
§35) with return time `g` satisfies the cycle equation with a defect `d ∈ (0, D]`:
`(3^g − 2^a) p = 2^a d − C_w`.

**`nearCycleAt_equation` (T1)** and **`finite_nearCycleAt` (T2).**  So each return time carries
only finitely many starts (finitely many words, and `3^g ≠ 2^a`).

**`card_fwdSurvivor_block_le` (NCU).**  If `U` had `N` orbits, a block `(Y, 2Y]` would hold at most
`N (1 + 2Y/D)` forward survivors plus the `D`-near-cycle starts in `(Y, 2Y)`.  On one orbit, the
survivors `n₁ < ⋯ < n_m` of the block are `pred`-linked (§31's P′); a gap `≤ D` makes the lower
end a near-cycle start, and fewer than `Y/D` gaps exceed `D`.  This contains NC′ (§35).

**`infinitelyManyOrbits_of_linearNearCycleLaw`.**  Measured: `NC_D` looks finite with
`#NC_D ≈ κ D`, `κ ≈ 5.07` an explicit random-walk constant (Conjecture LIN, BELIEVED 85%).  Under
LIN, NCU with `D ≈ √Y` gives (a) unless forward survivors in `(Y, 2Y]` are `O(√Y)`; measured
density `0.21`.
-/

namespace CollatzMoonshot.Amusical

/-- `p` is a `D`-near-cycle start with return time `g`. -/
def NearCycleAt (D p g : ℕ) : Prop :=
  1 ≤ g ∧ (p : ℤ) < amusical^[g] p ∧ amusical^[g] p ≤ p + D ∧
    ∀ k, 1 ≤ k → k < g → (p : ℤ) + D < amusical^[k] p

/-- **Target.**  Near-cycle starts are monotone in `D`. -/
theorem nearCycleStart_mono {D D' p : ℕ} (h : D ≤ D') (hp : NearCycleStart D p) :
    NearCycleStart D' p := by
  sorry

/-- **Target (T1).**  The near-cycle equation: the cycle equation with defect
`amusical^[g] p − p`. -/
theorem nearCycleAt_equation {D p g : ℕ} (h : NearCycleAt D p g) :
    ∃ (a : ℕ) (C : ℤ), 2 ^ a * amusical^[g] (p : ℤ) = 3 ^ g * p + C ∧
      ((3 : ℤ) ^ g - 2 ^ a) * p = 2 ^ a * (amusical^[g] (p : ℤ) - p) - C := by
  sorry

/-- **Target (T2).**  Each return time carries finitely many near-cycle starts. -/
theorem finite_nearCycleAt (D g : ℕ) : {p : ℕ | NearCycleAt D p g}.Finite := by
  sorry

open Classical in
/-- **Target (NCU).**  With finitely many orbits, forward survivors in a block are bounded by
`N (1 + 2Y/D)` plus the near-cycle starts in the block. -/
theorem card_fwdSurvivor_block_le (hfin : ¬ AmusicalInfinitelyManyOrbits) :
    ∃ N : ℕ, ∀ Y D : ℕ, 1 ≤ D →
      (((Finset.Ioc Y (2 * Y)).filter fun n : ℕ => FwdSurvivor n).card : ℝ) ≤
        N * (1 + 2 * (Y : ℝ) / D) +
          ((Finset.Ioo Y (2 * Y)).filter (NearCycleStart D)).card := by
  sorry

/-- **Open (Conjecture LIN, BELIEVED 85%).**  Near-cycle starts are finite for each `D`, and their
number grows linearly in `D`. -/
def LinearNearCycleLaw : Prop :=
  (∀ D : ℕ, {p : ℕ | NearCycleStart D p}.Finite) ∧ ∃ κ : ℝ,
    Filter.Tendsto (fun D : ℕ => (Nat.card {p : ℕ // NearCycleStart D p} : ℝ) / D)
      Filter.atTop (nhds κ)

open Classical in
/-- **Target.**  Under LIN, Klamkin (a) follows unless forward survivors per block are
`O(√Y)`. -/
theorem infinitelyManyOrbits_of_linearNearCycleLaw (hLIN : LinearNearCycleLaw)
    (hFS : ∀ C : ℝ, ∃ Y : ℕ, C * Real.sqrt Y <
      ((Finset.Ioc Y (2 * Y)).filter fun n : ℕ => FwdSurvivor n).card) :
    AmusicalInfinitelyManyOrbits := by
  sorry

end CollatzMoonshot.Amusical
