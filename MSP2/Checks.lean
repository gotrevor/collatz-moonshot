/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import MSP2.Hypothesis

/-!
# MSP²: the article's numbers, checked

Every worked example and table entry we could state without the Generator Table itself,
checked by evaluation.  All of them hold.
-/

namespace MSP2

open CollatzMoonshot

/-- §15.9 / §16.2: the vertical loop at coefficient `9`, `4 → 2 → 1 → 5 → 7 → 8 → 4`. -/
theorem tA_nine_loop :
    (List.range 7).map (fun i => (tA 9)^[i] 4) = [4, 2, 1, 5, 7, 8, 4] := by native_decide

/-- §16.2: the 18-state vertical loop at coefficient `27`. -/
theorem tA_twentyseven_loop :
    (List.range 19).map (fun i => (tA 27)^[i] 22) =
      [22, 11, 19, 23, 25, 26, 13, 20, 10, 5, 16, 8, 4, 2, 1, 14, 7, 17, 22] := by native_decide

/-- §9.9: the first blocking points. -/
theorem blockB_values : (List.range 4).map blockB = [25, 385, 6145, 98305] := by native_decide

/-- §16.3-16.4: the B constants. -/
theorem bConst_values : (List.range 6).map bConst = [4, 13, 40, 121, 364, 1093] := by
  native_decide

/-- §16.5: the left-route constants. -/
theorem cLeft_values : (List.range 6).map cLeft = [1, 22, 13, 202, 121, 1822] := by
  native_decide

/-- §16.7.4: the first cousin offsets, `Δ_1 = −16` and `Δ_2 = 38` being the jumps
`18k+14 ↦ 54k+26` and `54k+14 ↦ 162k+80` worked in §16.4. -/
theorem delta_values : (List.range 5).map delta = [2, -16, 38, -124, 362] := by native_decide

/-- Table 5 (§16.3): useful distances `1 → B` at `A = 9, 27, …, 2187` are
`4, 10, 28, 82, 244, 730`. -/
theorem table5_distances :
    (List.range 6).map (fun n => (tA (3 ^ (n + 2)))^[3 ^ (n + 1) + 1] 1) =
      (List.range 6).map bConst ∧
    (List.range 6).all (fun n =>
      (List.range (3 ^ (n + 1) + 1)).all (fun i => (tA (3 ^ (n + 2)))^[i] 1 != bConst n)) := by
  native_decide

/-- Table 8 (§16.5): distances `6, 18, 54, 162, 486` between the two sides, alternating
direction. -/
theorem table8_distances :
    (List.range 5).all (fun m =>
      if m % 2 = 0 then (tA (3 ^ (m + 3)))^[2 * 3 ^ (m + 1)] (cLeft (m + 1)) == bConst (m + 1)
      else (tA (3 ^ (m + 3)))^[2 * 3 ^ (m + 1)] (bConst (m + 1)) == cLeft (m + 1)) := by
  native_decide

/-- Tables 4, 6, 9 (§16.2-16.5): the row bounds, from the article's three formulas
`n+1+2·3^(n−1)`, `n+2+3^(n−1)`, `n+1+2·3^(n−2)` at `n = 3, …, 7` (starts up to 7 … 127). -/
theorem tables_4_6_9 :
    (List.range 5).map (fun i => let n := i + 3; n + 1 + 2 * 3 ^ (n - 1)) =
      [22, 59, 168, 493, 1466] ∧
    (List.range 5).map (fun i => let n := i + 3; n + 2 + 3 ^ (n - 1)) =
      [14, 33, 88, 251, 738] ∧
    (List.range 5).map (fun i => let n := i + 3; n + 1 + 2 * 3 ^ (n - 2)) =
      [10, 23, 60, 169, 494] := by
  native_decide

/-- §19: the three loops of MSP²⁻ on the negative integers. -/
theorem msp2Neg_loops :
    (List.range 12).map (fun i => msp2Neg^[i] (-17)) =
      [-17, -25, -37, -55, -82, -41, -61, -91, -136, -68, -34, -17] ∧
    (List.range 4).map (fun i => msp2Neg^[i] (-5)) = [-5, -7, -10, -5] ∧
    msp2Neg (-1) = -1 := by
  native_decide

/-- The article's worked levels (starts up to 7, 15, 31, 63, 127) are covered; the
slowest start is `27`, which first dips below itself after 96 steps. -/
theorem covered_upto_127 : ∀ N, N < 128 → 2 ≤ N → ∃ j, j < 97 ∧ step^[j] N < N := by
  native_decide

theorem raccordLevel_seven : RaccordLevel 7 := by
  intro N h2 hN
  obtain ⟨j, -, hj⟩ := covered_upto_127 N (by simp at hN; omega) h2
  exact ⟨j, hj⟩

end MSP2
