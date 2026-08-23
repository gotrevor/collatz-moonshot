/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.BackwardHeightTransfer

/-!
# The correlated 270-state exponent-`2/3` local transfer certificate

The exact net-height exponent-`1/2` certificate in `BackwardHeightTransfer`
treats the ternary digit forgotten by `y = (2^j x - 1) / 3` adversarially and
*independently* for every child.  That correlation is real: all children of one
source `x` share the single next ternary digit of `x`.  Writing
`x = r + t·3^4 (mod 3^5)` and `Q = (2^j r - 1) / 3`, the cost-`j` child
satisfies

  `y = Q + 2^j · t · 3^3  (mod 3^4)`,

so the fixed carry digit already present in `Q` must be retained while one
shared digit `t` steers every child at once.  This file kernel-checks the
frozen 270-state certificate from `experiments/barrier_transfer.py`: states are
unit residues modulo `81` times the five height floors `{1, 7/4, 5/2, 3, 4}`,
and for each of the three source lifts the weighted child sum strictly expands
with the rational edge underweight

  `(52/25) · (629/1000)^j < (3 / 2^j)^(2/3)`,

valid because `(52/25)^3 < 9` and `4 · (629/1000)^3 < 1`.  All `270 × 3 = 810`
inequalities are checked by the kernel on an integer-scaled form (scale
`25 · 1000^23`); no `native_decide` and no new axiom is used.  The acceptance
theorem `exists_twoThirdsExpansion` connects the table to actual, distinct,
floor-safe Collatz children of an arbitrary reusable parent.
-/

namespace CollatzMoonshot.FrontA

/-! ## The five height floors -/

/-- Numerators of the five height floors `1, 7/4, 5/2, 3, 4`. -/
def fiveHeightNum (i : Fin 5) : ℕ :=
  if i.1 = 0 then 1 else if i.1 = 1 then 7 else if i.1 = 2 then 5
  else if i.1 = 3 then 3 else 4

/-- Denominators of the five height floors `1, 7/4, 5/2, 3, 4`. -/
def fiveHeightDen (i : Fin 5) : ℕ :=
  if i.1 = 1 then 4 else if i.1 = 2 then 2 else 1

/-- The five-state height floor `x/d ≥ num i / den i`, without division. -/
def InFiveHeightState (d : ℕ) (i : Fin 5) (x : ℕ) : Prop :=
  fiveHeightNum i * d ≤ fiveHeightDen i * x

/-- Every height floor is at least `1`, so every state stays above `d`. -/
theorem InFiveHeightState.le {d x : ℕ} {i : Fin 5}
    (h : InFiveHeightState d i x) : d ≤ x := by
  unfold InFiveHeightState fiveHeightNum fiveHeightDen at h
  fin_cases i <;> simp_all <;> omega

/-- The five-state height transition used for a growing child of cost `j ≥ 2`.
Bins are computed from the uniform bound `y/d ≥ (2^j·h - 1/2)/3` for `d ≥ 2`. -/
def nextGrowingFiveState (i : Fin 5) (j : ℕ) : Fin 5 :=
  if i.1 = 0 then (if j ≤ 2 then 0 else if j = 3 then 2 else 4)
  else if i.1 = 4 then 4
  else if j ≤ 2 then (if i.1 = 1 then 1 else 3)
  else 4

/-- The five-state height transition for the shrinking `j = 1` child. -/
def shrinkFiveState (i : Fin 5) : Fin 5 :=
  if i.1 = 4 then 2 else if i.1 = 3 then 1 else 0

/-- Whether this finite state may use the safe shrinking `j = 1` child:
the height floor must be at least `7/4` and the source class integral unit. -/
def fiveHasShrink (i : Fin 5) (r : ℕ) : Bool :=
  decide (1 ≤ i.1) && (r % 9 == 2 || r % 9 == 8)

/-- Floor-safe five-state transition for an actual growing odd block. -/
theorem fiveHeightStep_growing {d x y j : ℕ} {i : Fin 5} (hd : 2 ≤ d)
    (hj : 2 ≤ j) (hstate : InFiveHeightState d i x)
    (hblock : 3 * y + 1 = 2 ^ j * x) :
    InFiveHeightState d (nextGrowingFiveState i j) y := by
  simp only [InFiveHeightState, fiveHeightNum, fiveHeightDen,
    nextGrowingFiveState] at hstate ⊢
  by_cases h2 : j ≤ 2
  · have hj2 : j = 2 := le_antisymm h2 hj
    subst hj2
    norm_num at hblock
    fin_cases i <;> simp_all <;> omega
  · by_cases h3 : j = 3
    · subst h3
      norm_num at hblock
      fin_cases i <;> simp_all <;> omega
    · have h16 : (16 : ℕ) ≤ 2 ^ j := by
        calc (16 : ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h16x : 16 * x ≤ 3 * y + 1 := by
        rw [hblock]
        exact Nat.mul_le_mul_right x h16
      clear hblock
      simp only [if_neg h2, if_neg h3]
      fin_cases i <;> simp_all <;> omega

/-- Floor-safe five-state transition for the actual shrinking `j = 1` block,
available at every floor of height at least `7/4`. -/
theorem fiveHeightStep_shrinking {d x y : ℕ} {i : Fin 5} (hd : 2 ≤ d)
    (hi : 1 ≤ i.1) (hstate : InFiveHeightState d i x)
    (hblock : 3 * y + 1 = 2 * x) :
    InFiveHeightState d (shrinkFiveState i) y := by
  simp only [InFiveHeightState, fiveHeightNum, fiveHeightDen,
    shrinkFiveState] at hstate ⊢
  fin_cases i <;> simp_all <;> omega

/-! ## The shared next ternary digit -/

/-- The child residue modulo `81` determined by the source modulo `243`,
including the fixed carry digit produced by the division `(2^j r - 1) / 3`. -/
def twoThirdsChildResidue (r j : ℕ) : ℕ :=
  ((2 ^ j * (r % 243) - 1) / 3) % 81

/-- An actual odd inverse block has the child residue predicted by
`twoThirdsChildResidue`. -/
theorem oddBlockChild_mod_eightyOne {x y j : ℕ}
    (h : 3 * y + 1 = 2 ^ j * x) :
    y % 81 = twoThirdsChildResidue x j := by
  unfold twoThirdsChildResidue
  have hx : x % 243 + 243 * (x / 243) = x := Nat.mod_add_div x 243
  have hp : 0 < 2 ^ j := pow_pos (by omega) _
  have heq :
      3 * y + 1 =
        2 ^ j * (x % 243) + 243 * (2 ^ j * (x / 243)) := by
    calc
      3 * y + 1 = 2 ^ j * x := h
      _ = 2 ^ j * (x % 243 + 243 * (x / 243)) :=
        congrArg (fun z => 2 ^ j * z) hx.symm
      _ = 2 ^ j * (x % 243) + 243 * (2 ^ j * (x / 243)) := by ring
  have hr : 0 < x % 243 := by
    by_contra hz
    have hz' : x % 243 = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz', mul_zero, zero_add] at heq
    omega
  have hpr : 0 < 2 ^ j * (x % 243) := Nat.mul_pos hp hr
  let z := 2 ^ j * (x / 243)
  have hzle : 81 * z ≤ y := by
    dsimp [z]
    omega
  have hnum : 2 ^ j * (x % 243) - 1 = 3 * (y - 81 * z) := by
    dsimp [z]
    omega
  have ha : (2 ^ j * (x % 243) - 1) / 3 = y - 81 * z := by
    rw [hnum]
    omega
  rw [ha]
  omega

/-- The child residue seen from a state residue modulo `81` together with one
shared next ternary digit `t` of the source. -/
def sharedLiftChildResidue (r j t : ℕ) : ℕ :=
  twoThirdsChildResidue (r % 81 + 81 * (t % 3)) j

/-- The single shared digit really controls every actual child: an odd block
from `x` lands in the residue class selected by `t = x / 81 % 3`. -/
theorem oddBlockChild_sharedLift {x y j : ℕ}
    (h : 3 * y + 1 = 2 ^ j * x) :
    y % 81 = sharedLiftChildResidue x j (x / 81 % 3) := by
  rw [oddBlockChild_mod_eightyOne h]
  unfold sharedLiftChildResidue twoThirdsChildResidue
  have h243 : (x % 81 + 81 * (x / 81 % 3 % 3)) % 243 = x % 243 := by omega
  rw [h243]

theorem sharedLiftChildResidue_mod_left (x j t : ℕ) :
    sharedLiftChildResidue (x % 81) j t = sharedLiftChildResidue x j t := by
  unfold sharedLiftChildResidue
  rw [Nat.mod_mod_of_dvd x dvd_rfl]

theorem sharedLiftChildResidue_mod_right (x j t : ℕ) :
    sharedLiftChildResidue x j (t % 3) = sharedLiftChildResidue x j t := by
  unfold sharedLiftChildResidue
  rw [Nat.mod_mod_of_dvd t dvd_rfl]

/-! ## The frozen 270-entry potential -/

private def twoThirdsPot0 (r : ℕ) : ℕ :=
  match r % 81 with
  | 1 => 461753 | 2 => 223157 | 4 => 354780 | 5 => 319087 | 7 => 225411 | 8 => 131094
  | 10 => 290624 | 11 => 375318 | 13 => 166953 | 14 => 358364 | 16 => 208416 | 17 => 114782
  | 19 => 432633 | 20 => 170055 | 22 => 249164 | 23 => 284972 | 25 => 171167 | 26 => 112746
  | 28 => 394347 | 29 => 203733 | 31 => 314233 | 32 => 331345 | 34 => 182484 | 35 => 167449
  | 37 => 371464 | 38 => 292251 | 40 => 153316 | 41 => 340602 | 43 => 200706 | 44 => 141783
  | 46 => 453055 | 47 => 229355 | 49 => 314767 | 50 => 272126 | 52 => 179247 | 53 => 107664
  | 55 => 461235 | 56 => 197653 | 58 => 323900 | 59 => 416101 | 61 => 214239 | 62 => 126244
  | 64 => 526780 | 65 => 370729 | 67 => 169907 | 68 => 290117 | 70 => 266215 | 71 => 134756
  | 73 => 401835 | 74 => 296972 | 76 => 228221 | 77 => 252754 | 79 => 158983 | 80 => 100000
  | _ => 0

private def twoThirdsPot1 (r : ℕ) : ℕ :=
  match r % 81 with
  | 1 => 523834 | 2 => 734142 | 4 => 354780 | 5 => 319087 | 7 => 225411 | 8 => 564071
  | 10 => 385367 | 11 => 720355 | 13 => 364635 | 14 => 358364 | 16 => 208416 | 17 => 500446
  | 19 => 432633 | 20 => 462104 | 22 => 596690 | 23 => 284972 | 25 => 171167 | 26 => 265436
  | 28 => 471039 | 29 => 733322 | 31 => 314233 | 32 => 331345 | 34 => 182484 | 35 => 514959
  | 37 => 562831 | 38 => 687920 | 40 => 270357 | 41 => 340602 | 43 => 200706 | 44 => 396148
  | 46 => 453055 | 47 => 837558 | 49 => 589394 | 50 => 272126 | 52 => 179247 | 53 => 270131
  | 55 => 461235 | 56 => 626973 | 58 => 323900 | 59 => 423235 | 61 => 214239 | 62 => 499604
  | 64 => 526780 | 65 => 638945 | 67 => 472134 | 68 => 290117 | 70 => 266215 | 71 => 362855
  | 73 => 401835 | 74 => 590676 | 76 => 464628 | 77 => 252754 | 79 => 158983 | 80 => 243754
  | _ => 0

private def twoThirdsPot2 (r : ℕ) : ℕ :=
  match r % 81 with
  | 1 => 541497 | 2 => 734142 | 4 => 354780 | 5 => 319087 | 7 => 225411 | 8 => 564071
  | 10 => 507293 | 11 => 720355 | 13 => 668875 | 14 => 358364 | 16 => 208416 | 17 => 500446
  | 19 => 432633 | 20 => 462104 | 22 => 684050 | 23 => 284972 | 25 => 171167 | 26 => 265436
  | 28 => 569735 | 29 => 733322 | 31 => 314233 | 32 => 331345 | 34 => 182484 | 35 => 514959
  | 37 => 661528 | 38 => 687920 | 40 => 420981 | 41 => 340602 | 43 => 200706 | 44 => 396148
  | 46 => 453055 | 47 => 837558 | 49 => 589394 | 50 => 272126 | 52 => 179247 | 53 => 270131
  | 55 => 461235 | 56 => 626973 | 58 => 323900 | 59 => 423235 | 61 => 214239 | 62 => 499604
  | 64 => 526780 | 65 => 638945 | 67 => 472134 | 68 => 290117 | 70 => 266215 | 71 => 362855
  | 73 => 401835 | 74 => 590676 | 76 => 586555 | 77 => 252754 | 79 => 158983 | 80 => 243754
  | _ => 0

private def twoThirdsPot3 (r : ℕ) : ℕ :=
  match r % 81 with
  | 1 => 541497 | 2 => 832839 | 4 => 354780 | 5 => 319087 | 7 => 225411 | 8 => 564071
  | 10 => 507293 | 11 => 720355 | 13 => 668875 | 14 => 358364 | 16 => 208416 | 17 => 937060
  | 19 => 432633 | 20 => 612728 | 22 => 684050 | 23 => 284972 | 25 => 171167 | 26 => 579716
  | 28 => 569735 | 29 => 733322 | 31 => 314233 | 32 => 331345 | 34 => 182484 | 35 => 514959
  | 37 => 661528 | 38 => 687920 | 40 => 420981 | 41 => 340602 | 43 => 200706 | 44 => 948653
  | 46 => 453055 | 47 => 837558 | 49 => 589394 | 50 => 272126 | 52 => 179247 | 53 => 750619
  | 55 => 461235 | 56 => 748900 | 58 => 323900 | 59 => 423235 | 61 => 214239 | 62 => 499604
  | 64 => 526780 | 65 => 638945 | 67 => 472134 | 68 => 290117 | 70 => 266215 | 71 => 738702
  | 73 => 401835 | 74 => 894916 | 76 => 586555 | 77 => 252754 | 79 => 158983 | 80 => 429829
  | _ => 0

private def twoThirdsPot4 (r : ℕ) : ℕ :=
  match r % 81 with
  | 1 => 541497 | 2 => 860930 | 4 => 354780 | 5 => 319087 | 7 => 225411 | 8 => 564071
  | 10 => 507293 | 11 => 720355 | 13 => 668875 | 14 => 358364 | 16 => 208416 | 17 => 937060
  | 19 => 432633 | 20 => 806569 | 22 => 684050 | 23 => 284972 | 25 => 171167 | 26 => 579716
  | 28 => 569735 | 29 => 733322 | 31 => 314233 | 32 => 331345 | 34 => 182484 | 35 => 514959
  | 37 => 672870 | 38 => 687920 | 40 => 420981 | 41 => 340602 | 43 => 200706 | 44 => 948653
  | 46 => 453055 | 47 => 837558 | 49 => 589394 | 50 => 272126 | 52 => 179247 | 53 => 750619
  | 55 => 461235 | 56 => 905810 | 58 => 323900 | 59 => 423235 | 61 => 214239 | 62 => 499604
  | 64 => 526780 | 65 => 638945 | 67 => 472134 | 68 => 290117 | 70 => 266215 | 71 => 738702
  | 73 => 401835 | 74 => 1051827 | 76 => 743466 | 77 => 252754 | 79 => 158983 | 80 => 429829
  | _ => 0

/-- The frozen positive integer potential attached to a height/residue state,
copied from `experiments/barrier_transfer.py` in its documented order. -/
def twoThirdsPotential (i : Fin 5) (r : ℕ) : ℕ :=
  if i.1 = 0 then twoThirdsPot0 r else if i.1 = 1 then twoThirdsPot1 r
  else if i.1 = 2 then twoThirdsPot2 r else if i.1 = 3 then twoThirdsPot3 r
  else twoThirdsPot4 r

/-- The state potential depends only on the residue modulo `81`. -/
theorem twoThirdsPotential_mod (i : Fin 5) (x : ℕ) :
    twoThirdsPotential i (x % 81) = twoThirdsPotential i x := by
  have h : x % 81 % 81 = x % 81 := Nat.mod_mod_of_dvd x dvd_rfl
  simp only [twoThirdsPotential, twoThirdsPot0, twoThirdsPot1, twoThirdsPot2,
    twoThirdsPot3, twoThirdsPot4, h]

/-- Every reusable residue has strictly positive potential at every floor. -/
theorem twoThirdsPotential_pos_of_unit :
    ∀ i : Fin 5, ∀ r : Fin 81, r.1 % 3 ≠ 0 →
      0 < twoThirdsPotential i r.1 := by
  decide +kernel

/-! ## The kernel-checked integer certificate -/

theorem sevenCostsAt_le_twentyThree (x : ℕ) (k : Fin 7) :
    sevenCostsAt x k ≤ 23 :=
  (sevenCostsAt_le_sevenTransferCost x k).trans
    (by fin_cases k <;> norm_num [sevenTransferCost])

theorem sevenCostsAt_mod_eightyOne (x : ℕ) :
    sevenCostsAt (x % 81) = sevenCostsAt x := by
  unfold sevenCostsAt
  rw [Nat.mod_mod_of_dvd x (by norm_num : 9 ∣ 81)]

theorem fiveHasShrink_mod_eightyOne (i : Fin 5) (x : ℕ) :
    fiveHasShrink i (x % 81) = fiveHasShrink i x := by
  unfold fiveHasShrink
  rw [Nat.mod_mod_of_dvd x (by norm_num : 9 ∣ 81)]

/-- One integer-scaled growing edge of the transfer image: the true edge
weight `(52/25)·(629/1000)^j` is cleared to scale `25 · 1000^23`. -/
def twoThirdsNatEdge (i : Fin 5) (r t j : ℕ) : ℕ :=
  629 ^ j * 1000 ^ (23 - j) *
    twoThirdsPotential (nextGrowingFiveState i j) (sharedLiftChildResidue r j t)

/-- The integer-scaled one-generation transfer image at one source lift. -/
def twoThirdsNatImage (i : Fin 5) (r t : ℕ) : ℕ :=
  52 * (twoThirdsNatEdge i r t (sevenCostsAt r 0) +
    twoThirdsNatEdge i r t (sevenCostsAt r 1) +
    twoThirdsNatEdge i r t (sevenCostsAt r 2) +
    twoThirdsNatEdge i r t (sevenCostsAt r 3) +
    twoThirdsNatEdge i r t (sevenCostsAt r 4) +
    twoThirdsNatEdge i r t (sevenCostsAt r 5) +
    twoThirdsNatEdge i r t (sevenCostsAt r 6) +
    if fiveHasShrink i r then
      629 * 1000 ^ 22 *
        twoThirdsPotential (shrinkFiveState i) (sharedLiftChildResidue r 1 t)
    else 0)

set_option maxRecDepth 8000 in
/-- All `810` source-state/lift inequalities of the frozen certificate, in
kernel-checked integer form at scale `25 · 1000^23`. -/
theorem twoThirdsNatCertificate :
    ∀ i : Fin 5, ∀ t : Fin 3, ∀ r : Fin 81, r.1 % 3 ≠ 0 →
      25 * 1000 ^ 23 * twoThirdsPotential i r.1 <
        twoThirdsNatImage i r.1 t.1 := by
  decide +kernel

/-! ## The rational certificate -/

/-- The rational one-generation transfer image at one source lift, with the
exact edge underweight `(52/25) · (629/1000)^j`. -/
def twoThirdsImage (i : Fin 5) (r t : ℕ) : ℚ :=
  (52 / 25 : ℚ) *
    (∑ k : Fin 7, (629 / 1000 : ℚ) ^ sevenCostsAt r k *
        twoThirdsPotential (nextGrowingFiveState i (sevenCostsAt r k))
          (sharedLiftChildResidue r (sevenCostsAt r k) t) +
      if fiveHasShrink i r then
        (629 / 1000 : ℚ) *
          twoThirdsPotential (shrinkFiveState i) (sharedLiftChildResidue r 1 t)
      else 0)

theorem twoThirdsImage_mod (i : Fin 5) (x t : ℕ) :
    twoThirdsImage i (x % 81) (t % 3) = twoThirdsImage i x t := by
  unfold twoThirdsImage
  simp only [sevenCostsAt_mod_eightyOne, sharedLiftChildResidue_mod_left,
    sharedLiftChildResidue_mod_right, fiveHasShrink_mod_eightyOne]

private theorem qpow_scale {j : ℕ} (hj : j ≤ 23) :
    ((629 : ℚ) / 1000) ^ j * 1000 ^ 23 = 629 ^ j * 1000 ^ (23 - j) := by
  have hsplit : (1000 : ℚ) ^ 23 = 1000 ^ j * 1000 ^ (23 - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hcancel : ((629 : ℚ) / 1000) ^ j * 1000 ^ j = 629 ^ j := by
    rw [div_pow]
    field_simp
  rw [hsplit, ← mul_assoc, hcancel]

/-- The integer-scaled image is exactly `25 · 1000^23` times the rational
image. -/
theorem twoThirdsNatImage_eq (i : Fin 5) (r t : ℕ) :
    (twoThirdsNatImage i r t : ℚ) = 25 * 1000 ^ 23 * twoThirdsImage i r t := by
  have h0 := qpow_scale (sevenCostsAt_le_twentyThree r 0)
  have h1 := qpow_scale (sevenCostsAt_le_twentyThree r 1)
  have h2 := qpow_scale (sevenCostsAt_le_twentyThree r 2)
  have h3 := qpow_scale (sevenCostsAt_le_twentyThree r 3)
  have h4 := qpow_scale (sevenCostsAt_le_twentyThree r 4)
  have h5 := qpow_scale (sevenCostsAt_le_twentyThree r 5)
  have h6 := qpow_scale (sevenCostsAt_le_twentyThree r 6)
  unfold twoThirdsNatImage twoThirdsNatEdge twoThirdsImage
  rw [Fin.sum_univ_seven]
  by_cases hs : fiveHasShrink i r = true <;>
    simp only [hs, if_true, Bool.false_eq_true, if_false] <;>
    push_cast <;>
    rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6] <;>
    ring

/-- The rational certificate at an arbitrary reusable source and arbitrary
shared lift digit. -/
theorem twoThirdsPotentialCertificateAt (i : Fin 5) {x : ℕ} (h3 : ¬3 ∣ x)
    (t : ℕ) : (twoThirdsPotential i x : ℚ) < twoThirdsImage i x t := by
  have hr81 : x % 81 < 81 := Nat.mod_lt x (by norm_num)
  have hru : (x % 81) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd x (by norm_num : 3 ∣ 81)]
    exact fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0)
  have hnat := twoThirdsNatCertificate i ⟨t % 3, Nat.mod_lt t (by norm_num)⟩
    ⟨x % 81, hr81⟩ hru
  have hq : (twoThirdsPotential i (x % 81) : ℚ) <
      twoThirdsImage i (x % 81) (t % 3) := by
    have hcast : ((25 * 1000 ^ 23 * twoThirdsPotential i (x % 81) : ℕ) : ℚ) <
        (twoThirdsNatImage i (x % 81) (t % 3) : ℚ) := by
      exact_mod_cast hnat
    rw [twoThirdsNatImage_eq] at hcast
    push_cast at hcast
    have hpos : (0 : ℚ) < 25 * 1000 ^ 23 := by norm_num
    exact lt_of_mul_lt_mul_left (by linarith) (le_of_lt hpos)
  rw [twoThirdsPotential_mod, twoThirdsImage_mod] at hq
  exact hq

/-- The two elementary comparisons behind the rational edge underweight. -/
theorem twoThirdsRationalUnderestimate :
    (52 / 25 : ℚ) ^ 3 < 9 ∧ 4 * (629 / 1000 : ℚ) ^ 3 < 1 := by
  norm_num

/-! ## The actual-child acceptance theorem -/

/-- **Correlated exponent-`2/3` local expansion.**  Every reusable source
`x ≥ 2`, `3 ∤ x` in any of the five height states over an arbitrary floor
`d ≥ 2` has its exact seven distinct growing odd children, plus the actual
shrinking `j = 1` child precisely when the finite certificate enables it; all
children satisfy their Collatz block equations and floor-safe five-state
transitions, growing children stay below `2^23 x` in the sense
`3y < 2^23 x`, and the frozen potential strictly expands with the exact
rational weight `(52/25) · (629/1000)^j` over the actual child states. -/
theorem exists_twoThirdsExpansion {d x : ℕ} (i : Fin 5) (hd : 2 ≤ d)
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InFiveHeightState d i x) :
    ∃ (ys : Fin 7 → ℕ) (z : ℕ), Function.Injective ys ∧
      (∀ k, GrowingUnitOddBlockChild x (ys k) (sevenCostsAt x k) ∧
        InFiveHeightState d (nextGrowingFiveState i (sevenCostsAt x k)) (ys k) ∧
        3 * ys k < 2 ^ 23 * x) ∧
      (fiveHasShrink i x = true →
        UnitOddBlockChildAtOne x z ∧
        InFiveHeightState d (shrinkFiveState i) z ∧
        ∀ k, z ≠ ys k) ∧
      (twoThirdsPotential i x : ℚ) <
        (52 / 25 : ℚ) *
          (∑ k : Fin 7, (629 / 1000 : ℚ) ^ sevenCostsAt x k *
              twoThirdsPotential
                (nextGrowingFiveState i (sevenCostsAt x k)) (ys k) +
            if fiveHasShrink i x then
              (629 / 1000 : ℚ) *
                twoThirdsPotential (shrinkFiveState i) z
            else 0) := by
  obtain ⟨ys, hys, hch⟩ := exactSevenCostTransferAt hx h3
  have hcert := twoThirdsPotentialCertificateAt i h3 (x / 81 % 3)
  have hgrow : ∀ k, GrowingUnitOddBlockChild x (ys k) (sevenCostsAt x k) ∧
      InFiveHeightState d (nextGrowingFiveState i (sevenCostsAt x k)) (ys k) ∧
      3 * ys k < 2 ^ 23 * x := by
    intro k
    refine ⟨hch k, fiveHeightStep_growing hd (hch k).1 hstate (hch k).2.2.2.2, ?_⟩
    have hc := sevenCostsAt_le_twentyThree x k
    have hple : (2 : ℕ) ^ sevenCostsAt x k ≤ 2 ^ 23 :=
      Nat.pow_le_pow_right (by norm_num) hc
    have hmul : 2 ^ sevenCostsAt x k * x ≤ 2 ^ 23 * x :=
      Nat.mul_le_mul_right x hple
    have hb := (hch k).2.2.2.2
    omega
  have hpotEq : ∀ k : Fin 7,
      twoThirdsPotential (nextGrowingFiveState i (sevenCostsAt x k))
        (sharedLiftChildResidue x (sevenCostsAt x k) (x / 81 % 3)) =
      twoThirdsPotential (nextGrowingFiveState i (sevenCostsAt x k)) (ys k) := by
    intro k
    rw [← oddBlockChild_sharedLift (hch k).2.2.2.2, twoThirdsPotential_mod]
  by_cases hs : fiveHasShrink i x = true
  · have hrem : x % 9 = 2 ∨ x % 9 = 8 := by
      unfold fiveHasShrink at hs
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hs
      exact hs.2
    have hi1 : 1 ≤ i.1 := by
      unfold fiveHasShrink at hs
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hs
      exact hs.1
    obtain ⟨z, hz⟩ := exists_unitOddBlockChildAtOne hrem
    have hzblock : 3 * z + 1 = 2 ^ 1 * x := by
      have := hz.2.2.2
      norm_num
      omega
    have hz81 :
        twoThirdsPotential (shrinkFiveState i)
          (sharedLiftChildResidue x 1 (x / 81 % 3)) =
        twoThirdsPotential (shrinkFiveState i) z := by
      rw [← oddBlockChild_sharedLift hzblock, twoThirdsPotential_mod]
    refine ⟨ys, z, hys, hgrow, fun _ =>
      ⟨hz, fiveHeightStep_shrinking hd hi1 hstate hz.2.2.2, fun k hzy => ?_⟩, ?_⟩
    · have hzlt := hz.2.2.1
      have hylt := (hch k).2.2.2.1
      omega
    · have himg : twoThirdsImage i x (x / 81 % 3) =
          (52 / 25 : ℚ) *
            (∑ k : Fin 7, (629 / 1000 : ℚ) ^ sevenCostsAt x k *
                twoThirdsPotential
                  (nextGrowingFiveState i (sevenCostsAt x k)) (ys k) +
              if fiveHasShrink i x then
                (629 / 1000 : ℚ) *
                  twoThirdsPotential (shrinkFiveState i) z
              else 0) := by
        unfold twoThirdsImage
        rw [Finset.sum_congr rfl fun k _ => by rw [hpotEq k]]
        simp only [hs, if_true, hz81]
      exact himg ▸ hcert
  · refine ⟨ys, 0, hys, hgrow, fun hcontra => absurd hcontra hs, ?_⟩
    have himg : twoThirdsImage i x (x / 81 % 3) =
        (52 / 25 : ℚ) *
          (∑ k : Fin 7, (629 / 1000 : ℚ) ^ sevenCostsAt x k *
              twoThirdsPotential
                (nextGrowingFiveState i (sevenCostsAt x k)) (ys k) +
            if fiveHasShrink i x then
              (629 / 1000 : ℚ) *
                twoThirdsPotential (shrinkFiveState i) 0
            else 0) := by
      unfold twoThirdsImage
      rw [Finset.sum_congr rfl fun k _ => by rw [hpotEq k]]
      rw [Bool.not_eq_true] at hs
      simp only [hs, Bool.false_eq_true, if_false]
    exact himg ▸ hcert

end CollatzMoonshot.FrontA
