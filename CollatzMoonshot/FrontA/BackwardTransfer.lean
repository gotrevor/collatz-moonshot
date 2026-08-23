/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.BackwardBranching

/-!
# Variable-cost transfer certificates in the barriered backward tree

The first binary subtree charged every reusable odd inverse block the worst
possible cost `j = 7`.  Here the exponent `j` is retained as a height cost.
The unit-child pattern is controlled by the parent modulo `9` and is periodic
in `j` with period `6`; its coordinatewise worst cost stream begins
`5, 7, 11, 13, 17, 19, 23`.
-/

namespace CollatzMoonshot.FrontA

/-- A reusable growing odd inverse block with its logarithmic ceiling cost
recorded explicitly. -/
def GrowingUnitOddBlockChild (x y j : ℕ) : Prop :=
  2 ≤ j ∧ y % 2 = 1 ∧ ¬3 ∣ y ∧ x < y ∧ 3 * y + 1 = 2 ^ j * x

/-- A costed growing child reaches its parent without dropping below it and
with exact multiplicative ceiling `2^j`. -/
theorem GrowingUnitOddBlockChild.reachesInBand {x y j : ℕ}
    (h : GrowingUnitOddBlockChild x y j) : ReachesInBand x (2 ^ j * x) y := by
  obtain ⟨_, hyodd, _, hxy, hblock⟩ := h
  exact reachesInBand_of_odd_block hyodd hxy.le hblock

/-- For a fixed positive parent, the child determines its cost exponent. -/
theorem growingUnitOddBlockChild_cost_eq_of_child_eq {x y y' j j' : ℕ}
    (hx : 0 < x) (h : GrowingUnitOddBlockChild x y j)
    (h' : GrowingUnitOddBlockChild x y' j') (hyy' : y = y') : j = j' := by
  obtain ⟨_, _, _, _, hblock⟩ := h
  obtain ⟨_, _, _, _, hblock'⟩ := h'
  have hpowers : 2 ^ j * x = 2 ^ j' * x := by omega
  have hpow : 2 ^ j = 2 ^ j' := Nat.eq_of_mul_eq_mul_right hx hpowers
  exact Nat.pow_right_injective (by norm_num) hpow

/-- Children of distinct odd parents cannot collide, with no upper bound on
the two cost exponents. -/
theorem growingUnitOddBlockChild_parent_eq {x x' y j j' : ℕ}
    (hx : x % 2 = 1) (hx' : x' % 2 = 1)
    (h : GrowingUnitOddBlockChild x y j)
    (h' : GrowingUnitOddBlockChild x' y j') : x = x' := by
  obtain ⟨_, _, _, _, hblock⟩ := h
  obtain ⟨_, _, _, _, hblock'⟩ := h'
  have heq : 2 ^ j * x = 2 ^ j' * x' := by omega
  rcases le_total j j' with hle | hle
  · exact parent_eq_of_exp_le hx hle heq
  · exact (parent_eq_of_exp_le hx' hle heq.symm).symm

/-- Coordinatewise worst costs for the first seven reusable growing children
over the six unit residue classes modulo `9`. -/
def sevenTransferCost : Fin 7 → ℕ := ![5, 7, 11, 13, 17, 19, 23]

/-- A labeled seven-child variable-cost certificate at one parent. -/
def SevenCostTransferAt (x : ℕ) : Prop :=
  ∃ ys js : Fin 7 → ℕ, Function.Injective ys ∧
    (∀ i, GrowingUnitOddBlockChild x (ys i) (js i)) ∧
    ∀ i, js i ≤ sevenTransferCost i

private theorem makeSevenCostTransfer {x : ℕ} (hx : 0 < x)
    (ys js : Fin 7 → ℕ) (hjs : Function.Injective js)
    (hchildren : ∀ i, GrowingUnitOddBlockChild x (ys i) (js i))
    (hcost : ∀ i, js i ≤ sevenTransferCost i) : SevenCostTransferAt x := by
  refine ⟨ys, js, ?_, hchildren, hcost⟩
  intro i i' hii'
  apply hjs
  exact growingUnitOddBlockChild_cost_eq_of_child_eq hx
    (hchildren i) (hchildren i') hii'

private theorem sevenCostTransfer_mod9_one (q : ℕ) (hx : 2 ≤ 9 * q + 1) :
    SevenCostTransferAt (9 * q + 1) := by
  let ys : Fin 7 → ℕ :=
    ![12 * q + 1, 48 * q + 5, 768 * q + 85, 3072 * q + 341,
      49152 * q + 5461, 196608 * q + 21845, 3145728 * q + 349525]
  let js : Fin 7 → ℕ := ![2, 4, 8, 10, 14, 16, 20]
  apply makeSevenCostTransfer (by omega) ys js
  · dsimp [js]
    decide
  · intro i
    fin_cases i <;> dsimp [ys, js]
    all_goals
      unfold GrowingUnitOddBlockChild
      refine ⟨by norm_num, by omega, by omega, by omega, ?_⟩
      norm_num
      ring
  · intro i
    fin_cases i <;> norm_num [js, sevenTransferCost]

private theorem sevenCostTransfer_mod9_two (q : ℕ) (hx : 2 ≤ 9 * q + 2) :
    SevenCostTransferAt (9 * q + 2) := by
  let ys : Fin 7 → ℕ :=
    ![24 * q + 5, 384 * q + 85, 1536 * q + 341, 24576 * q + 5461,
      98304 * q + 21845, 1572864 * q + 349525, 6291456 * q + 1398101]
  let js : Fin 7 → ℕ := ![3, 7, 9, 13, 15, 19, 21]
  apply makeSevenCostTransfer (by omega) ys js
  · dsimp [js]
    decide
  · intro i
    fin_cases i <;> dsimp [ys, js]
    all_goals
      unfold GrowingUnitOddBlockChild
      refine ⟨by norm_num, by omega, by omega, by omega, ?_⟩
      norm_num
      ring
  · intro i
    fin_cases i <;> norm_num [js, sevenTransferCost]

private theorem sevenCostTransfer_mod9_four (q : ℕ) (hx : 2 ≤ 9 * q + 4) :
    SevenCostTransferAt (9 * q + 4) := by
  let ys : Fin 7 → ℕ :=
    ![12 * q + 5, 192 * q + 85, 768 * q + 341, 12288 * q + 5461,
      49152 * q + 21845, 786432 * q + 349525, 3145728 * q + 1398101]
  let js : Fin 7 → ℕ := ![2, 6, 8, 12, 14, 18, 20]
  apply makeSevenCostTransfer (by omega) ys js
  · dsimp [js]
    decide
  · intro i
    fin_cases i <;> dsimp [ys, js]
    all_goals
      unfold GrowingUnitOddBlockChild
      refine ⟨by norm_num, by omega, by omega, by omega, ?_⟩
      norm_num
      ring
  · intro i
    fin_cases i <;> norm_num [js, sevenTransferCost]

private theorem sevenCostTransfer_mod9_five (q : ℕ) (hx : 2 ≤ 9 * q + 5) :
    SevenCostTransferAt (9 * q + 5) := by
  let ys : Fin 7 → ℕ :=
    ![24 * q + 13, 96 * q + 53, 1536 * q + 853, 6144 * q + 3413,
      98304 * q + 54613, 393216 * q + 218453, 6291456 * q + 3495253]
  let js : Fin 7 → ℕ := ![3, 5, 9, 11, 15, 17, 21]
  apply makeSevenCostTransfer (by omega) ys js
  · dsimp [js]
    decide
  · intro i
    fin_cases i <;> dsimp [ys, js]
    all_goals
      unfold GrowingUnitOddBlockChild
      refine ⟨by norm_num, by omega, by omega, by omega, ?_⟩
      norm_num
      ring
  · intro i
    fin_cases i <;> norm_num [js, sevenTransferCost]

private theorem sevenCostTransfer_mod9_seven (q : ℕ) (hx : 2 ≤ 9 * q + 7) :
    SevenCostTransferAt (9 * q + 7) := by
  let ys : Fin 7 → ℕ :=
    ![48 * q + 37, 192 * q + 149, 3072 * q + 2389, 12288 * q + 9557,
      196608 * q + 152917, 786432 * q + 611669, 12582912 * q + 9786709]
  let js : Fin 7 → ℕ := ![4, 6, 10, 12, 16, 18, 22]
  apply makeSevenCostTransfer (by omega) ys js
  · dsimp [js]
    decide
  · intro i
    fin_cases i <;> dsimp [ys, js]
    all_goals
      unfold GrowingUnitOddBlockChild
      refine ⟨by norm_num, by omega, by omega, by omega, ?_⟩
      norm_num
      ring
  · intro i
    fin_cases i <;> norm_num [js, sevenTransferCost]

private theorem sevenCostTransfer_mod9_eight (q : ℕ) (hx : 2 ≤ 9 * q + 8) :
    SevenCostTransferAt (9 * q + 8) := by
  let ys : Fin 7 → ℕ :=
    ![96 * q + 85, 384 * q + 341, 6144 * q + 5461, 24576 * q + 21845,
      393216 * q + 349525, 1572864 * q + 1398101, 25165824 * q + 22369621]
  let js : Fin 7 → ℕ := ![5, 7, 11, 13, 17, 19, 23]
  apply makeSevenCostTransfer (by omega) ys js
  · dsimp [js]
    decide
  · intro i
    fin_cases i <;> dsimp [ys, js]
    all_goals
      unfold GrowingUnitOddBlockChild
      refine ⟨by norm_num, by omega, by omega, by omega, ?_⟩
      norm_num
      ring
  · intro i
    fin_cases i <;> norm_num [js, sevenTransferCost]

/-- Every unit modulo `3` above `1` has seven distinct reusable growing odd
children with individual height costs bounded by `5,7,11,13,17,19,23`.
The bounds are sharp coordinatewise: the class `x = 8 mod 9` attains them. -/
theorem sevenCostTransferAt {x : ℕ} (hx : 2 ≤ x) (h3 : ¬3 ∣ x) :
    SevenCostTransferAt x := by
  have hlt : x % 9 < 9 := Nat.mod_lt x (by norm_num)
  have hrepr : x % 9 + 9 * (x / 9) = x := Nat.mod_add_div x 9
  interval_cases hrem : x % 9
  · exfalso
    apply h3
    use 3 * (x / 9)
    omega
  · rw [← hrepr]
    simpa [Nat.add_comm] using sevenCostTransfer_mod9_one (x / 9) (by omega)
  · rw [← hrepr]
    simpa [Nat.add_comm] using sevenCostTransfer_mod9_two (x / 9) (by omega)
  · exfalso
    apply h3
    use 3 * (x / 9) + 1
    omega
  · rw [← hrepr]
    simpa [Nat.add_comm] using sevenCostTransfer_mod9_four (x / 9) (by omega)
  · rw [← hrepr]
    simpa [Nat.add_comm] using sevenCostTransfer_mod9_five (x / 9) (by omega)
  · exfalso
    apply h3
    use 3 * (x / 9) + 2
    omega
  · rw [← hrepr]
    simpa [Nat.add_comm] using sevenCostTransfer_mod9_seven (x / 9) (by omega)
  · rw [← hrepr]
    simpa [Nat.add_comm] using sevenCostTransfer_mod9_eight (x / 9) (by omega)

/-- The exact rational inequality behind the finite transfer certificate. -/
theorem sevenCostWeightCertificate :
    (5 / 6 : ℚ) ^ 5 + (5 / 6 : ℚ) ^ 7 + (5 / 6 : ℚ) ^ 11 +
      (5 / 6 : ℚ) ^ 13 + (5 / 6 : ℚ) ^ 17 + (5 / 6 : ℚ) ^ 19 +
      (5 / 6 : ℚ) ^ 23 > 1 := by
  norm_num

end CollatzMoonshot.FrontA
