/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycleLaw.Block

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

/-- **Proved.**  Near-cycle starts are monotone in `D` (the new return time is the first
re-entry of `[0, p + D']`). -/
theorem nearCycleStart_mono {D D' p : ℕ} (h : D ≤ D') (hp : NearCycleStart D p) :
    NearCycleStart D' p :=
  NearCycleLaw.nearCycleStart_mono_aux h hp

/-- **Proved (T1).**  The near-cycle equation: the cycle equation with defect
`amusical^[g] p − p`. -/
theorem nearCycleAt_equation {D p g : ℕ} (h : NearCycleAt D p g) :
    ∃ (a : ℕ) (C : ℤ), 2 ^ a * amusical^[g] (p : ℤ) = 3 ^ g * p + C ∧
      ((3 : ℤ) ^ g - 2 ^ a) * p = 2 ^ a * (amusical^[g] (p : ℤ) - p) - C := by
  obtain ⟨a, C, -, -, -, heq⟩ := amusical_iterate_affine g p
  exact ⟨a, C, heq, by linear_combination -heq⟩

/-- **Proved (T2).**  Each return time carries finitely many near-cycle starts: by Lemma K
(`abs_le_four_pow_mul_iterate_sub`), `p ≤ 4ᵍ (D + 1)`. -/
theorem finite_nearCycleAt (D g : ℕ) : {p : ℕ | NearCycleAt D p g}.Finite := by
  refine (Set.finite_Iic (4 ^ g * (D + 1))).subset fun p hp => ?_
  obtain ⟨hg, h1, h2, -⟩ := hp
  have hK := (abs_le_four_pow_mul_iterate_sub g hg p).1
  rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ p), abs_of_pos (by omega)] at hK
  have h4 : (4 : ℤ) ^ g * (amusical^[g] (p : ℤ) - p + 1) ≤ 4 ^ g * (D + 1) := by
    gcongr; omega
  simp only [Set.mem_Iic]
  exact_mod_cast hK.trans h4

open Classical in
/-- **Proved (NCU).**  With finitely many orbits, forward survivors in a block are bounded by
`N (1 + 2Y/D)` plus the near-cycle starts in the block (`N = 3r`, `r` the number of orbits;
see `NearCycleLaw.card_fwdSurvivor_block_le_nat`). -/
theorem card_fwdSurvivor_block_le (hfin : ¬ AmusicalInfinitelyManyOrbits) :
    ∃ N : ℕ, ∀ Y D : ℕ, 1 ≤ D →
      (((Finset.Ioc Y (2 * Y)).filter fun n : ℕ => FwdSurvivor n).card : ℝ) ≤
        N * (1 + 2 * (Y : ℝ) / D) +
          ((Finset.Ioo Y (2 * Y)).filter (NearCycleStart D)).card := by
  obtain ⟨r, hr⟩ := NearCycleLaw.card_fwdSurvivor_block_le_nat hfin
  refine ⟨3 * r, fun Y D hD => ?_⟩
  have h := hr Y D hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hdiv : (((2 * Y + 1) / D : ℕ) : ℝ) ≤ 2 * (Y : ℝ) / D + 1 := by
    refine Nat.cast_div_le.trans ?_
    push_cast
    rw [add_div]
    gcongr
    rw [div_le_one hDpos]; exact hD1
  have hR : (((Finset.Ioc Y (2 * Y)).filter fun n : ℕ => FwdSurvivor n).card : ℝ) ≤
      2 * r + r * (((2 * Y + 1) / D : ℕ) : ℝ) +
        ((Finset.Ioo Y (2 * Y)).filter (NearCycleStart D)).card := by
    exact_mod_cast h
  have hY : 0 ≤ 2 * (Y : ℝ) / D := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hdiv hr0]

/-- **Open (Conjecture LIN, BELIEVED 85%).**  Near-cycle starts are finite for each `D`, and their
number grows linearly in `D`. -/
def LinearNearCycleLaw : Prop :=
  (∀ D : ℕ, {p : ℕ | NearCycleStart D p}.Finite) ∧ ∃ κ : ℝ,
    Filter.Tendsto (fun D : ℕ => (Nat.card {p : ℕ // NearCycleStart D p} : ℝ) / D)
      Filter.atTop (nhds κ)

open Classical in
/-- **Proved.**  Under LIN, Klamkin (a) follows unless forward survivors per block are
`O(√Y)`.  LIN gives `#NC_D ≤ K D` for `D ≥ 1` (`NearCycleLaw.exists_card_nearCycleStart_le`);
NCU at `D = ⌈√Y⌉` gives `#FS ≤ (3N + 2K) √Y`. -/
theorem infinitelyManyOrbits_of_linearNearCycleLaw (hLIN : LinearNearCycleLaw)
    (hFS : ∀ C : ℝ, ∃ Y : ℕ, C * Real.sqrt Y <
      ((Finset.Ioc Y (2 * Y)).filter fun n : ℕ => FwdSurvivor n).card) :
    AmusicalInfinitelyManyOrbits := by
  by_contra hfin
  obtain ⟨N, hN⟩ := card_fwdSurvivor_block_le hfin
  obtain ⟨hLf, κ, hκ⟩ := hLIN
  obtain ⟨K, hK⟩ := NearCycleLaw.exists_card_nearCycleStart_le hLf hκ
  obtain ⟨Y, hY⟩ := hFS (3 * N + 2 * K)
  rcases Nat.eq_zero_or_pos Y with rfl | hY0
  · simp at hY
  set s := Real.sqrt Y with hs
  have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY0
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hY1
  have hss : s * s = Y := Real.mul_self_sqrt (by positivity)
  set D := ⌈s⌉₊ with hDdef
  have hsD : s ≤ D := Nat.le_ceil s
  have hDs : (D : ℝ) < s + 1 := Nat.ceil_lt_add_one (by linarith)
  have hD1 : 1 ≤ D := by exact_mod_cast hs1.trans hsD
  have hDpos : (0 : ℝ) < D := by linarith
  have hNC := (NearCycleLaw.card_nearCycleStart_block_le (hLf D) Y).trans (hK D hD1)
  have hNC' : (((Finset.Ioo Y (2 * Y)).filter (NearCycleStart D)).card : ℝ) ≤ K * D := by
    exact_mod_cast hNC
  have hYD : (Y : ℝ) / D ≤ s := by
    rw [div_le_iff₀ hDpos, ← hss]
    exact mul_le_mul_of_nonneg_left hsD (by linarith)
  have h := hN Y D hD1
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have h2 : (N : ℝ) * (1 + 2 * (Y : ℝ) / D) ≤ N * (3 * s) := by
    apply mul_le_mul_of_nonneg_left _ hN0
    rw [mul_div_assoc]
    linarith
  have h3 : (K : ℝ) * D ≤ K * (2 * s) := mul_le_mul_of_nonneg_left (by linarith) hK0
  push_cast at hY
  linarith

end CollatzMoonshot.Amusical
