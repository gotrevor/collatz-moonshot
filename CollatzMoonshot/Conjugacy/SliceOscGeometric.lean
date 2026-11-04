/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.BeyondWordsLinear

/-!
# The `levelOsc` probe: a geometric form of the sliced Proposition 1.14

`experiments/conjugacy/levelosc_table.js` (output `levelosc_table.out`) tabulates the exact
ratio `levelOsc j a m / #levelSet j a` for `j = 10, …, 26`, `|a − j/2| ≤ 2`, `1 ≤ m ≤ a`.  The
shape at the central slice `a = j/2`:

* at fixed co-scale `a − m` the ratio falls with `j` (`a − m = 1`: `0.259, 0.229, 0.211, 0.188,
  0.164, 0.144, 0.127, 0.111, 0.098` for `j = 10, …, 26`), about `0.88` per added digit;
* at fixed `m` it rises with `j` toward a limit, with geometrically shrinking increments
  (`m = 3`: `0.441 → 0.585`, increments `0.040, 0.033, …, 0.006`; extrapolated limit `≈ 0.61`);
  the extrapolated limits fall roughly geometrically in `m` (ratio `≈ 0.86`).

So the data are consistent with the node and suggest the stronger geometric form
`SliceOscGeometric` (frozen below, conjecture).  Caveat: near the sparse edge `a ≈ 3j/5` of the
window the slice has fewer starts than points of `ℤ/3^a` for every `j ≤ 26` (and up to
`j ≈ 210`), where the ratio at small `m` is `≈ 1.4–1.7`; a geometric `θ` must then be close to
`1`, so the data do not pin `θ`.  No claim beyond the table.

`sliceOscDecay_of_geometric`: the geometric form implies the node (`m^N θ^m` is bounded).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- **Conjecture node (probe-suggested, 2026-11-04).**  Geometric decay of the slice oscillation
in the 3-adic scale, uniformly on the window `j ≤ 5a ≤ 3j`.  Evidence: the exact table
`experiments/conjugacy/levelosc_table.out` (`j ≤ 26`), central-slice ratio `≈ 0.86–0.88` per
digit; control: `m = a` gives `0`.  Confidence 55% (the sparse edge may force `θ → 1`); it
implies `SliceOscDecay` (`sliceOscDecay_of_geometric`). -/
def SliceOscGeometric : Prop :=
  ∃ C > (0 : ℝ), ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ j a m : ℕ, 1 ≤ m → m ≤ a → j ≤ 5 * a →
    5 * a ≤ 3 * j → levelOsc j a m ≤ C * θ ^ m * (levelSet j a).card

/-- **Edge.**  Geometric decay of the slice oscillation gives the sliced Proposition 1.14 at every
exponent: `θ^m ≤ B m^{−⌈A⌉} ≤ B m^{−A}`. -/
theorem sliceOscDecay_of_geometric (h : SliceOscGeometric) : SliceOscDecay := by
  obtain ⟨C, hC, θ, hθ0, hθ1, hb⟩ := h
  intro A hA
  set N := ⌈A⌉₊ with hN
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one N
    (by rw [abs_of_nonneg hθ0]; exact hθ1)
  obtain ⟨B, hB⟩ := ht.bddAbove_range
  have hB0 : 0 ≤ B := by
    have := hB ⟨0, rfl⟩
    exact le_trans (by positivity) this
  refine ⟨C * (B + 1), by positivity, ?_⟩
  intro j a m hm1 hma hw1 hw2
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmpos : (0 : ℝ) < m := by linarith
  have hfm : (m : ℝ) ^ N * θ ^ m ≤ B := hB ⟨m, rfl⟩
  have hθm : θ ^ m ≤ (B + 1) * (m : ℝ) ^ (-A) := by
    have hpowpos : (0 : ℝ) < (m : ℝ) ^ N := by positivity
    have hle : (m : ℝ) ^ (-(N : ℝ)) ≤ (m : ℝ) ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_le hmR (by linarith [Nat.le_ceil A])
    rw [Real.rpow_neg hmpos.le, Real.rpow_natCast] at hle
    have h1 : θ ^ m ≤ B * ((m : ℝ) ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpowpos]
      linarith
    have h2 : 0 ≤ (m : ℝ) ^ (-A) := by positivity
    calc
      θ ^ m ≤ B * ((m : ℝ) ^ N)⁻¹ := h1
      _ ≤ B * (m : ℝ) ^ (-A) := by gcongr
      _ ≤ (B + 1) * (m : ℝ) ^ (-A) := by nlinarith
  have hcard : (0 : ℝ) ≤ (levelSet j a).card := by positivity
  calc
    levelOsc j a m ≤ C * θ ^ m * (levelSet j a).card := hb j a m hm1 hma hw1 hw2
    _ ≤ C * ((B + 1) * (m : ℝ) ^ (-A)) * (levelSet j a).card := by gcongr
    _ = C * (B + 1) * (m : ℝ) ^ (-A) * (levelSet j a).card := by ring

end CollatzMoonshot.Conjugacy
