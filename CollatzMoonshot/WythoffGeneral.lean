/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The Wythoff (Beatty-merge) map `W_α` on `ℤ`, for every real `α > 1`

The family of research note `wythoff`: `W_α(2k) = ⌊kα⌋`, `W_α(2k − 1) = ⌊kβ⌋`,
`β = α/(α − 1)` (so `1/α + 1/β = 1`).  On all of `ℤ` we use Mathlib's `beattySeq'` on the odd
branch, `2k − 1 ↦ ⌈kβ⌉ − 1`: by Rayleigh's theorem (`compl_beattySeq`) the two branches then have
complementary ranges for **every** `α > 1`, rational or not, so `wy α` is a permutation of `ℤ`
preserving `ℕ⁺` (`wy_bijective`, `wy_pos_iff`).  For irrational `α` and `k ≠ 0` the odd branch is
the floor `⌊kβ⌋` of the research notes (`wy_two_mul_sub_one_eq_floor`); for rational `α` it is
the "`−`" limit member.

This file is the shared base of `WythoffCone` (Theorems A′ and K, research note `wythoff-2adic`)
and `WythoffLine` (Theorem G, research note `wythoff-solvable`).  It also records the two
equidistribution theorems of Weyl used for densities, as **literature hypotheses** (not in
Mathlib): `WeylEquidistribution` (one dimension) and `WeylEquidistributionMulti`.
-/

namespace CollatzMoonshot.WythoffGeneral

open Filter Topology

/-- The Wythoff map on `ℤ`: `2k ↦ ⌊kα⌋`, `2k − 1 ↦ ⌈kβ⌉ − 1` with `β = α/(α − 1)`. -/
noncomputable def wy (α : ℝ) (n : ℤ) : ℤ :=
  if n % 2 = 0 then ⌊((n / 2 : ℤ) : ℝ) * α⌋
  else ⌈(((n + 1) / 2 : ℤ) : ℝ) * (α / (α - 1))⌉ - 1

section Branches

variable {α : ℝ}

/-- **(ratified).**  Even branch. -/
theorem wy_two_mul (α : ℝ) (k : ℤ) : wy α (2 * k) = ⌊(k : ℝ) * α⌋ := by
  unfold wy
  rw [if_pos (by omega), show 2 * k / 2 = k by omega]

/-- **(ratified).**  Odd branch. -/
theorem wy_two_mul_sub_one (α : ℝ) (k : ℤ) :
    wy α (2 * k - 1) = ⌈(k : ℝ) * (α / (α - 1))⌉ - 1 := by
  unfold wy
  rw [if_neg (by omega), show (2 * k - 1 + 1) / 2 = k by omega]

/-- **(ratified).**  `α` and `β = α/(α − 1)` are Hölder conjugate for `α > 1`
(`Real.HolderConjugate.conjExponent`). -/
theorem holderConjugate (hα : 1 < α) : α.HolderConjugate (α / (α - 1)) :=
  Real.HolderConjugate.conjExponent hα

/-- **(ratified).**  `W_α` is a bijection of `ℤ` for every `α > 1`.  Paper proof: the even branch
is `beattySeq α`, the odd branch `beattySeq' β`, both strictly increasing (`α, β > 1`), with
complementary ranges (`compl_beattySeq` with `holderConjugate`); the same argument as
`WythoffQuadratic.wq_bijective`. -/
theorem wy_bijective (hα : 1 < α) : Function.Bijective (wy α) := by
  sorry

/-- `W_α` as a permutation of `ℤ`. -/
noncomputable def wyPerm (α : ℝ) (hα : 1 < α) : Equiv.Perm ℤ :=
  Equiv.ofBijective (wy α) (wy_bijective hα)

theorem wyPerm_apply (hα : 1 < α) (n : ℤ) : wyPerm α hα n = wy α n := rfl

/-- **(ratified).**  `W_α` preserves `ℕ⁺` (and hence `ℤ≤0`).  Paper proof: for `k ≥ 1`,
`⌊kα⌋ ≥ k ≥ 1` and `kβ > 1` so `⌈kβ⌉ − 1 ≥ 1`; `W(0) = 0`, `W(−1) = ⌈0⌉ − 1 = −1`; for `k < 0`,
`⌊kα⌋ < 0` and `⌈kβ⌉ ≤ 0`. -/
theorem wy_pos_iff (hα : 1 < α) (n : ℤ) : 0 < wy α n ↔ 0 < n := by
  sorry

/-- **(ratified).**  For irrational `α` and `k ≠ 0`, the odd branch is the floor `⌊kβ⌋`
(`kβ ∉ ℤ` since `β = 1 + 1/(α − 1)` is irrational). -/
theorem wy_two_mul_sub_one_eq_floor (hα : 1 < α) (hirr : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    wy α (2 * k - 1) = ⌊(k : ℝ) * (α / (α - 1))⌋ := by
  sorry

/-- **(ratified).**  `1` is a fixed point once `α ≥ 2`: `W(1) = ⌈β⌉ − 1 = 1` as `1 < β ≤ 2`. -/
theorem wy_one (hα : 2 ≤ α) : wy α 1 = 1 := by
  sorry

/-- **(ratified).**  For `α ≥ 3`, positive evens step up: `W(2k) = ⌊kα⌋ ≥ 3k > 2k`. -/
theorem lt_wy_of_even (hα : 3 ≤ α) {z : ℤ} (hz : 0 < z) (he : z % 2 = 0) : z < wy α z := by
  sorry

/-- **(ratified).**  For `α ≥ 3`, odd `z ≥ 3` step down: `β ≤ 3/2`, so for `j ≥ 2`,
`jβ ≤ 2j − 1` and `⌈jβ⌉ − 1 < 2j − 1`. -/
theorem wy_lt_of_odd (hα : 3 ≤ α) {z : ℤ} (hz : 1 < z) (ho : z % 2 = 1) : wy α z < z := by
  sorry

/-- **(ratified).**  For `1 < α < 2`, positive evens step down: `⌊kα⌋ < 2k`. -/
theorem wy_lt_of_even (hα : α < 2) {z : ℤ} (hz : 0 < z) (he : z % 2 = 0) : wy α z < z := by
  sorry

/-- **(ratified).**  For `1 < α < 2`, positive odds step up: `β > 2`, so `⌈kβ⌉ − 1 ≥ 2k`. -/
theorem lt_wy_of_odd (hα1 : 1 < α) (hα : α < 2) {z : ℤ} (hz : 0 < z) (ho : z % 2 = 1) :
    z < wy α z := by
  sorry

end Branches

/-! ## Literature hypotheses: Weyl equidistribution -/

/-- **Literature hypothesis (Bohl 1909, Sierpiński 1910, Weyl 1910/1916; not in Mathlib).**  For
irrational `θ`, the fractional parts `{kθ}` are equidistributed in `[0, 1)`: every interval
`[a, b) ⊆ [0, 1]` is visited by `k ∈ [1, N]` with frequency tending to `b − a`. -/
def WeylEquidistribution : Prop :=
  ∀ θ : ℝ, Irrational θ → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter fun k : ℕ => Int.fract ((k : ℝ) * θ) ∈ Set.Ico a b).card : ℝ)
          / N)
      atTop (𝓝 (b - a))

open Classical in
/-- **Literature hypothesis (Weyl 1916, multidimensional; with the standard extension from boxes
to Jordan-measurable sets, Kuipers-Niederreiter, *Uniform Distribution of Sequences*, Ch. 1 §6;
not in Mathlib).**  If `1, θ₀, …, θ_{d−1}` are linearly independent over `ℚ`, the points
`({kθ₀}, …, {kθ_{d−1}})` are equidistributed in `[0, 1)^d`: every measurable `B` whose frontier
is Lebesgue-null is visited with frequency `vol(B ∩ [0, 1)^d)`. -/
def WeylEquidistributionMulti : Prop :=
  ∀ (d : ℕ) (θ : Fin d → ℝ), LinearIndependent ℚ (Fin.cons (1 : ℝ) θ : Fin (d + 1) → ℝ) →
    ∀ B : Set (Fin d → ℝ), MeasurableSet B → MeasureTheory.volume (frontier B) = 0 →
      Tendsto (fun N : ℕ =>
          (((Finset.Icc 1 N).filter fun k : ℕ =>
            (fun i => Int.fract ((k : ℝ) * θ i)) ∈ B).card : ℝ) / N)
        atTop (𝓝 (MeasureTheory.volume (B ∩ Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1)).toReal)

end CollatzMoonshot.WythoffGeneral
