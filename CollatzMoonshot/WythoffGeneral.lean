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

/-- `β = α/(α − 1) > 1`. -/
lemma one_lt_beta (hα : 1 < α) : 1 < α / (α - 1) := by
  rw [one_lt_div (by linarith)]; linarith

/-- The even branch `k ↦ ⌊kα⌋` is strictly increasing. -/
lemma floor_strictMono (hα : 1 < α) : StrictMono fun k : ℤ => ⌊(k : ℝ) * α⌋ := by
  refine strictMono_int_of_lt_succ fun k => ?_
  have h : (k : ℝ) * α + 1 ≤ ((k + 1 : ℤ) : ℝ) * α := by push_cast; nlinarith
  calc ⌊(k : ℝ) * α⌋ < ⌊(k : ℝ) * α⌋ + 1 := by omega
    _ = ⌊(k : ℝ) * α + 1⌋ := (Int.floor_add_one _).symm
    _ ≤ _ := Int.floor_mono h

/-- The odd branch `k ↦ ⌈kβ⌉ − 1` is strictly increasing. -/
lemma ceil_strictMono {γ : ℝ} (hγ : 1 < γ) : StrictMono fun k : ℤ => ⌈(k : ℝ) * γ⌉ - 1 := by
  refine strictMono_int_of_lt_succ fun k => ?_
  have h : (k : ℝ) * γ + 1 ≤ ((k + 1 : ℤ) : ℝ) * γ := by push_cast; nlinarith
  have : ⌈(k : ℝ) * γ⌉ + 1 ≤ ⌈((k + 1 : ℤ) : ℝ) * γ⌉ := by
    rw [← Int.ceil_add_one]; exact Int.ceil_mono h
  show ⌈(k : ℝ) * γ⌉ - 1 < ⌈((k + 1 : ℤ) : ℝ) * γ⌉ - 1
  omega

/-- **(ratified).**  `W_α` is a bijection of `ℤ` for every `α > 1`.  Paper proof: the even branch
is `beattySeq α`, the odd branch `beattySeq' β`, both strictly increasing (`α, β > 1`), with
complementary ranges (`compl_beattySeq` with `holderConjugate`); the same argument as
`WythoffQuadratic.wq_bijective`. -/
theorem wy_bijective (hα : 1 < α) : Function.Bijective (wy α) := by
  have hc := compl_beattySeq (holderConjugate hα)
  have hβ := one_lt_beta hα
  have cross : ∀ a b : ℤ, wy α (2 * a) ≠ wy α (2 * b - 1) := by
    intro a b h
    have hmem : beattySeq' (α / (α - 1)) b ∈ {x | ∃ k, beattySeq' (α / (α - 1)) k = x} :=
      ⟨b, rfl⟩
    rw [← hc] at hmem
    refine hmem ⟨a, ?_⟩
    simp only [beattySeq, beattySeq']
    rw [← wy_two_mul, ← wy_two_mul_sub_one, h]
  refine ⟨fun a b h => ?_, fun n => ?_⟩
  · obtain ⟨k, rfl | rfl⟩ : ∃ k, a = 2 * k ∨ a = 2 * k - 1 := ⟨(a + 1) / 2, by omega⟩ <;>
    obtain ⟨l, rfl | rfl⟩ : ∃ l, b = 2 * l ∨ b = 2 * l - 1 := ⟨(b + 1) / 2, by omega⟩
    · rw [wy_two_mul, wy_two_mul] at h; rw [(floor_strictMono hα).injective h]
    · exact absurd h (cross _ _)
    · exact absurd h.symm (cross _ _)
    · rw [wy_two_mul_sub_one, wy_two_mul_sub_one] at h
      rw [(ceil_strictMono hβ).injective h]
  · by_cases h : n ∈ {x | ∃ k, beattySeq α k = x}
    · obtain ⟨k, hk⟩ := h
      exact ⟨2 * k, by rw [wy_two_mul]; exact hk⟩
    · rw [← Set.mem_compl_iff, hc] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨2 * k - 1, by rw [wy_two_mul_sub_one]; exact hk⟩

/-- `W_α` as a permutation of `ℤ`. -/
noncomputable def wyPerm (α : ℝ) (hα : 1 < α) : Equiv.Perm ℤ :=
  Equiv.ofBijective (wy α) (wy_bijective hα)

theorem wyPerm_apply (hα : 1 < α) (n : ℤ) : wyPerm α hα n = wy α n := rfl

/-- **(ratified).**  `W_α` preserves `ℕ⁺` (and hence `ℤ≤0`).  Paper proof: for `k ≥ 1`,
`⌊kα⌋ ≥ k ≥ 1` and `kβ > 1` so `⌈kβ⌉ − 1 ≥ 1`; `W(0) = 0`, `W(−1) = ⌈0⌉ − 1 = −1`; for `k < 0`,
`⌊kα⌋ < 0` and `⌈kβ⌉ ≤ 0`. -/
theorem wy_pos_iff (hα : 1 < α) (n : ℤ) : 0 < wy α n ↔ 0 < n := by
  have hβ := one_lt_beta hα
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k - 1 := ⟨(n + 1) / 2, by omega⟩
  · rw [wy_two_mul, Int.floor_pos]
    rcases le_or_gt k 0 with hk | hk
    · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk
      constructor
      · intro h; nlinarith
      · intro h; omega
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      constructor
      · intro; omega
      · intro; nlinarith
  · rw [wy_two_mul_sub_one, sub_pos, Int.lt_ceil]
    push_cast
    rcases le_or_gt k 0 with hk | hk
    · have : (k : ℝ) ≤ 0 := by exact_mod_cast hk
      constructor
      · intro h; nlinarith
      · intro h; omega
    · have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      constructor
      · intro; omega
      · intro; nlinarith

/-- **(ratified).**  For irrational `α` and `k ≠ 0`, the odd branch is the floor `⌊kβ⌋`
(`kβ ∉ ℤ` since `β = 1 + 1/(α − 1)` is irrational). -/
theorem wy_two_mul_sub_one_eq_floor (hα : 1 < α) (hirr : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    wy α (2 * k - 1) = ⌊(k : ℝ) * (α / (α - 1))⌋ := by
  rw [wy_two_mul_sub_one]
  have hβ : α / (α - 1) = 1 + (α - 1)⁻¹ := by
    have : α - 1 ≠ 0 := by linarith
    field_simp; ring
  have hirr' : Irrational ((k : ℝ) * (α / (α - 1))) := by
    rw [hβ]
    have h1 : Irrational (α - 1) := by exact_mod_cast hirr.sub_intCast 1
    exact (h1.inv.intCast_add 1).intCast_mul hk |> fun h => by exact_mod_cast h
  have := (Int.ceil_eq_floor_add_one_iff_notMem _).mpr (fun ⟨z, hz⟩ => hirr'.ne_int z hz.symm)
  omega

/-- **(ratified).**  `1` is a fixed point once `α ≥ 2`: `W(1) = ⌈β⌉ − 1 = 1` as `1 < β ≤ 2`. -/
theorem wy_one (hα : 2 ≤ α) : wy α 1 = 1 := by
  have h1 : (1 : ℤ) = 2 * 1 - 1 := by norm_num
  rw [h1, wy_two_mul_sub_one]
  have hβ1 := one_lt_beta (by linarith : 1 < α)
  have hβ2 : α / (α - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have : ⌈((1 : ℤ) : ℝ) * (α / (α - 1))⌉ = 2 := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  omega

/-- **(ratified).**  For `α ≥ 3`, positive evens step up: `W(2k) = ⌊kα⌋ ≥ 3k > 2k`. -/
theorem lt_wy_of_even (hα : 3 ≤ α) {z : ℤ} (hz : 0 < z) (he : z % 2 = 0) : z < wy α z := by
  obtain ⟨k, rfl⟩ : ∃ k, z = 2 * k := ⟨z / 2, by omega⟩
  rw [wy_two_mul]
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  have : ((2 * k + 1 : ℤ) : ℝ) ≤ (k : ℝ) * α := by push_cast; nlinarith
  have := Int.le_floor.mpr this
  omega

/-- **(ratified).**  For `α ≥ 3`, odd `z ≥ 3` step down: `β ≤ 3/2`, so for `j ≥ 2`,
`jβ ≤ 2j − 1` and `⌈jβ⌉ − 1 < 2j − 1`. -/
theorem wy_lt_of_odd (hα : 3 ≤ α) {z : ℤ} (hz : 1 < z) (ho : z % 2 = 1) : wy α z < z := by
  obtain ⟨j, rfl⟩ : ∃ j, z = 2 * j - 1 := ⟨(z + 1) / 2, by omega⟩
  rw [wy_two_mul_sub_one]
  have hj : (2 : ℝ) ≤ j := by exact_mod_cast (show (2 : ℤ) ≤ j by omega)
  have hβ0 : 0 < α / (α - 1) := by have := one_lt_beta (by linarith : 1 < α); linarith
  have hβ2 : α / (α - 1) ≤ 3 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have : (j : ℝ) * (α / (α - 1)) ≤ ((2 * j - 1 : ℤ) : ℝ) := by push_cast; nlinarith
  have := Int.ceil_le.mpr this
  omega

/-- **(ratified).**  For `1 < α < 2`, positive evens step down: `⌊kα⌋ < 2k`. -/
theorem wy_lt_of_even (hα : α < 2) {z : ℤ} (hz : 0 < z) (he : z % 2 = 0) : wy α z < z := by
  obtain ⟨k, rfl⟩ : ∃ k, z = 2 * k := ⟨z / 2, by omega⟩
  rw [wy_two_mul]
  have hk : (0 : ℝ) < k := by exact_mod_cast (show (0 : ℤ) < k by omega)
  have : (k : ℝ) * α < ((2 * k : ℤ) : ℝ) := by push_cast; nlinarith
  exact Int.floor_lt.mpr this

/-- **(ratified).**  For `1 < α < 2`, positive odds step up: `β > 2`, so `⌈kβ⌉ − 1 ≥ 2k`. -/
theorem lt_wy_of_odd (hα1 : 1 < α) (hα : α < 2) {z : ℤ} (hz : 0 < z) (ho : z % 2 = 1) :
    z < wy α z := by
  obtain ⟨k, rfl⟩ : ∃ k, z = 2 * k - 1 := ⟨(z + 1) / 2, by omega⟩
  rw [wy_two_mul_sub_one]
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  have hβ2 : 2 < α / (α - 1) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have : ((2 * k : ℤ) : ℝ) < (k : ℝ) * (α / (α - 1)) := by push_cast; nlinarith
  have := Int.lt_ceil.mpr this
  omega

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

/-! ## Counting limits -/

/-- `⌊cX + d⌋₊ / X → c`. -/
lemma tendsto_floor_linear_div {c : ℝ} (hc : 0 < c) (d : ℝ) :
    Tendsto (fun X : ℕ => (⌊c * X + d⌋₊ : ℝ) / X) atTop (𝓝 c) := by
  have hlo : Tendsto (fun X : ℕ => c + (d - 1) / X) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (d - 1))
  have hhi : Tendsto (fun X : ℕ => c + d / X) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat d)
  have hev : ∀ᶠ X : ℕ in atTop, 0 ≤ c * X + d ∧ (0 : ℝ) < X := by
    obtain ⟨N, hN⟩ := exists_nat_gt (|d| / c)
    refine eventually_atTop.2 ⟨N + 1, fun X hX => ⟨?_, Nat.cast_pos.2 (by omega)⟩⟩
    have hX' : (N : ℝ) + 1 ≤ X := by exact_mod_cast hX
    have : |d| < c * X := by rw [div_lt_iff₀ hc] at hN; nlinarith
    linarith [neg_abs_le d]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hev] with X ⟨h0, hX⟩
    have := Nat.lt_floor_add_one (c * X + d)
    rw [le_div_iff₀ hX]
    have e : (c + (d - 1) / X) * X = c * X + d - 1 := by field_simp; ring
    linarith
  · filter_upwards [hev] with X ⟨h0, hX⟩
    have := Nat.floor_le h0
    rw [div_le_iff₀ hX]
    have e : (c + d / X) * X = c * X + d := by field_simp
    linarith

/-- Rescaling a counting limit: if `C(N)/N → L`, `f → ∞` and `f(X)/X → c`, then
`C(f(X))/X → L c`. -/
lemma tendsto_comp_div {C f : ℕ → ℕ} {L c : ℝ}
    (hC : Tendsto (fun N : ℕ => (C N : ℝ) / N) atTop (𝓝 L)) (hf : Tendsto f atTop atTop)
    (hfr : Tendsto (fun X : ℕ => (f X : ℝ) / X) atTop (𝓝 c)) :
    Tendsto (fun X : ℕ => (C (f X) : ℝ) / X) atTop (𝓝 (L * c)) := by
  refine ((hC.comp hf).mul hfr).congr' ?_
  filter_upwards [hf.eventually_ge_atTop 1] with X hX
  have : (f X : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  show (C (f X) : ℝ) / f X * (f X / X) = _
  rw [div_mul_div_cancel₀ this]

/-- `⌊c·X + d⌋₊ → ∞`. -/
lemma tendsto_floor_linear {c : ℝ} (hc : 0 < c) (d : ℝ) :
    Tendsto (fun X : ℕ => ⌊c * X + d⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_natCast_atTop_atTop.const_mul_atTop hc).atTop_add tendsto_const_nhds)

end CollatzMoonshot.WythoffGeneral
