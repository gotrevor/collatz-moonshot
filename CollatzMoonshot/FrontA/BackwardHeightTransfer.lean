/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.BackwardTransfer

/-!
# A two-height transfer certificate with the shrinking odd branch

The gross-cost certificate charges an odd block by `2^j`.  Successive odd
endpoints are instead related by `y = (2^j x - 1) / 3`; refunding that factor
`3` is essential.  This file kernel-checks the finite Collatz-specific data for
a net-height exponent `1/2` certificate.

There are two height states relative to a fixed floor `d`:

* low: `d ≤ x`;
* high: `7d ≤ 4x`.

A high parent may safely use an integral unit `j = 1` child, which returns to
the low state.  Every growing child of a high parent remains high, and a
growing child of cost at least `3` moves low to high.

The final rational table uses unit residues modulo `27`.  Division by `3`
forgets the next ternary digit, so each edge takes the minimum potential over
all three possible lifts.  The table is deliberately small enough for kernel
reduction: no `native_decide` axiom is used.
-/

namespace CollatzMoonshot.FrontA

/-- The high state `x/d ≥ 7/4`, written without division. -/
def HighAboveFloor (d x : ℕ) : Prop := 7 * d ≤ 4 * x

/-- The shrinking reusable odd block at exponent `j = 1`. -/
def UnitOddBlockChildAtOne (x y : ℕ) : Prop :=
  y % 2 = 1 ∧ ¬3 ∣ y ∧ y < x ∧ 3 * y + 1 = 2 * x

/-- Exactly the reusable `j = 1` source classes needed by the certificate have
an explicit shrinking unit child. -/
theorem exists_unitOddBlockChildAtOne {x : ℕ}
    (hrem : x % 9 = 2 ∨ x % 9 = 8) : ∃ y, UnitOddBlockChildAtOne x y := by
  have hrepr : x % 9 + 9 * (x / 9) = x := Nat.mod_add_div x 9
  rcases hrem with hrem | hrem
  · refine ⟨6 * (x / 9) + 1, ?_⟩
    unfold UnitOddBlockChildAtOne
    omega
  · refine ⟨6 * (x / 9) + 5, ?_⟩
    unfold UnitOddBlockChildAtOne
    omega

/-- A `j = 1` child of a high parent cannot cross the original floor. -/
theorem UnitOddBlockChildAtOne.aboveFloor {d x y : ℕ}
    (hx : HighAboveFloor d x) (h : UnitOddBlockChildAtOne x y) : d ≤ y := by
  unfold HighAboveFloor at hx
  obtain ⟨_, _, _, hblock⟩ := h
  omega

/-- Every growing child of a high parent remains high. -/
theorem GrowingUnitOddBlockChild.high_of_high {d x y j : ℕ}
    (hx : HighAboveFloor d x) (h : GrowingUnitOddBlockChild x y j) :
    HighAboveFloor d y := by
  unfold HighAboveFloor at hx ⊢
  obtain ⟨hj, _, _, _, hblock⟩ := h
  have hp : 4 ≤ 2 ^ j := by
    have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
    norm_num at this ⊢
    exact this
  have hmul : 4 * x ≤ 2 ^ j * x := Nat.mul_le_mul_right x hp
  omega

/-- From the low state, every growing child of cost at least `3` enters the
high state. -/
theorem GrowingUnitOddBlockChild.high_of_cost_ge_three {d x y j : ℕ}
    (hdx : d ≤ x) (hj3 : 3 ≤ j) (h : GrowingUnitOddBlockChild x y j) :
    HighAboveFloor d y := by
  unfold HighAboveFloor
  obtain ⟨_, _, _, _, hblock⟩ := h
  have hp : 8 ≤ 2 ^ j := by
    have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj3
    norm_num at this ⊢
    exact this
  have hmul : 8 * x ≤ 2 ^ j * x := Nat.mul_le_mul_right x hp
  omega

/-- Odd parents of a common odd-block child coincide, with no restriction on
either exponent.  This covers growing/growing, growing/shrinking, and
shrinking/shrinking collisions uniformly. -/
theorem oddBlock_parent_eq_of_odd {x x' y j j' : ℕ}
    (hx : x % 2 = 1) (hx' : x' % 2 = 1)
    (h : 3 * y + 1 = 2 ^ j * x) (h' : 3 * y + 1 = 2 ^ j' * x') :
    x = x' := by
  have heq : 2 ^ j * x = 2 ^ j' * x' := by omega
  rcases le_total j j' with hle | hle
  · exact parent_eq_of_exp_le hx hle heq
  · exact (parent_eq_of_exp_le hx' hle heq.symm).symm

/-- A low state records the original floor; a high state additionally records
the ratio lower bound `x/d ≥ 7/4`. -/
def InHeightState (d : ℕ) (high : Bool) (x : ℕ) : Prop :=
  d ≤ x ∧ (high = true → HighAboveFloor d x)

/-- The two-state height transition used for a growing child. -/
def nextGrowingHeightState (sourceHigh : Bool) (j : ℕ) : Bool :=
  sourceHigh || decide (3 ≤ j)

/-- The elementary height rules match the Boolean transition used by the
finite certificate. -/
theorem GrowingUnitOddBlockChild.in_nextHeightState {d x y j : ℕ}
    {high : Bool} (hx : InHeightState d high x)
    (h : GrowingUnitOddBlockChild x y j) :
    InHeightState d (nextGrowingHeightState high j) y := by
  constructor
  · obtain ⟨_, _, _, hxy, _⟩ := h
    exact hx.1.trans hxy.le
  · intro hnext
    cases high with
    | false =>
        simp only [nextGrowingHeightState, Bool.false_or] at hnext
        exact h.high_of_cost_ge_three hx.1 (of_decide_eq_true hnext)
    | true =>
        exact h.high_of_high (hx.2 rfl)

/-- The exact seven growing children also obey the certificate's two-state
height transition. -/
theorem exists_exactSevenHeightChildren {d x : ℕ} (high : Bool)
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InHeightState d high x) :
    ∃ ys : Fin 7 → ℕ, Function.Injective ys ∧
      ∀ i, GrowingUnitOddBlockChild x (ys i) (sevenCostsAt x i) ∧
        InHeightState d (nextGrowingHeightState high (sevenCostsAt x i)) (ys i) := by
  obtain ⟨ys, hys, hchildren⟩ := exactSevenCostTransferAt hx h3
  exact ⟨ys, hys, fun i =>
    ⟨hchildren i,
      GrowingUnitOddBlockChild.in_nextHeightState hstate (hchildren i)⟩⟩

/-- In either integral source class, a high state supplies the shrinking
`j = 1` child and that child returns to the low state. -/
theorem exists_shrinkingHeightChild {d x : ℕ} (hstate : InHeightState d true x)
    (hrem : x % 9 = 2 ∨ x % 9 = 8) :
    ∃ y, UnitOddBlockChildAtOne x y ∧ InHeightState d false y := by
  obtain ⟨y, hy⟩ := exists_unitOddBlockChildAtOne hrem
  refine ⟨y, hy, hy.aboveFloor (hstate.2 rfl), ?_⟩
  simp

/-! ## The exact 36-state rational potential -/

private def lowPotential (r : ℕ) : ℕ :=
  match r % 27 with
  | 1 => 140 | 2 => 76 | 4 => 108 | 5 => 99 | 7 => 78 | 8 => 48
  | 10 => 109 | 11 => 114 | 13 => 68 | 14 => 111 | 16 => 69 | 17 => 55
  | 19 => 132 | 20 => 77 | 22 => 99 | 23 => 92 | 25 => 65 | 26 => 45
  | _ => 0

private def highPotential (r : ℕ) : ℕ :=
  match r % 27 with
  | 1 => 159 | 2 => 200 | 4 => 108 | 5 => 99 | 7 => 78 | 8 => 154
  | 10 => 141 | 11 => 188 | 13 => 110 | 14 => 111 | 16 => 69 | 17 => 141
  | 19 => 132 | 20 => 155 | 22 => 163 | 23 => 92 | 25 => 65 | 26 => 97
  | _ => 0

/-- The positive integer potential attached to a height/residue state. -/
def netHalfStatePotential (high : Bool) (r : ℕ) : ℕ :=
  if high then highPotential r else lowPotential r

/-- The state potential depends only on the residue modulo `27`. -/
theorem netHalfStatePotential_mod_twentySeven (high : Bool) (x : ℕ) :
    netHalfStatePotential high (x % 27) = netHalfStatePotential high x := by
  cases high <;>
    simp [netHalfStatePotential, lowPotential, highPotential]

/-- Every reusable residue has strictly positive potential in either height
state. -/
theorem netHalfStatePotential_pos (high : Bool) {x : ℕ} (h3 : ¬3 ∣ x) :
    0 < netHalfStatePotential high x := by
  have hx3 : x % 3 ≠ 0 := fun hx0 => h3 (Nat.dvd_of_mod_eq_zero hx0)
  have hr : (x % 27) % 3 ≠ 0 := by
    rwa [Nat.mod_mod_of_dvd x (by norm_num : 3 ∣ 27)]
  rw [← netHalfStatePotential_mod_twentySeven high x]
  have hlt : x % 27 < 27 := Nat.mod_lt x (by norm_num)
  cases high <;> interval_cases hrem : x % 27 <;>
    norm_num [hrem] at hr <;>
    norm_num [netHalfStatePotential, lowPotential, highPotential, hrem]

/-- Every entry of the frozen potential table is at most `200`. -/
theorem netHalfStatePotential_le_twoHundred (high : Bool) (x : ℕ) :
    netHalfStatePotential high x ≤ 200 := by
  rw [← netHalfStatePotential_mod_twentySeven high x]
  have hlt : x % 27 < 27 := Nat.mod_lt x (by norm_num)
  cases high <;> interval_cases hrem : x % 27 <;>
    norm_num [netHalfStatePotential, lowPotential, highPotential, hrem]

/-- The child is determined modulo `9`; modulo `27` its forgotten next
ternary digit gives these three possible lifts. -/
def oddBlockChildResidueBase (r j : ℕ) : ℕ :=
  ((2 ^ j * (r % 27) - 1) / 3) % 9

/-- An actual odd inverse block has the residue predicted by
`oddBlockChildResidueBase`. -/
theorem oddBlockChild_mod_nine {x y j : ℕ}
    (h : 3 * y + 1 = 2 ^ j * x) :
    y % 9 = oddBlockChildResidueBase x j := by
  unfold oddBlockChildResidueBase
  have hx : x % 27 + 27 * (x / 27) = x := Nat.mod_add_div x 27
  have hp : 0 < 2 ^ j := pow_pos (by omega) _
  have heq :
      3 * y + 1 =
        2 ^ j * (x % 27) + 27 * (2 ^ j * (x / 27)) := by
    calc
      3 * y + 1 = 2 ^ j * x := h
      _ = 2 ^ j * (x % 27 + 27 * (x / 27)) :=
        congrArg (fun z => 2 ^ j * z) hx.symm
      _ = 2 ^ j * (x % 27) + 27 * (2 ^ j * (x / 27)) := by ring
  have hr : 0 < x % 27 := by
    by_contra hz
    have hz' : x % 27 = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz', mul_zero, zero_add] at heq
    omega
  have hpr : 0 < 2 ^ j * (x % 27) := Nat.mul_pos hp hr
  let z := 2 ^ j * (x / 27)
  have hzle : 9 * z ≤ y := by
    dsimp [z]
    omega
  have hnum : 2 ^ j * (x % 27) - 1 = 3 * (y - 9 * z) := by
    dsimp [z]
    omega
  have ha : (2 ^ j * (x % 27) - 1) / 3 = y - 9 * z := by
    rw [hnum]
    simp
  rw [ha]
  omega

/-- Knowing a residue modulo `9` leaves exactly three possible lifts modulo
`27`. -/
theorem residue_mod_twentySeven_lifts {y b : ℕ} (hb : y % 9 = b) :
    y % 27 = b ∨ y % 27 = b + 9 ∨ y % 27 = b + 18 := by
  have hm : (y % 27) % 9 = y % 9 :=
    Nat.mod_mod_of_dvd y (by norm_num : 9 ∣ 27)
  have hrepr : (y % 27) % 9 + 9 * ((y % 27) / 9) = y % 27 :=
    Nat.mod_add_div (y % 27) 9
  have hlt : y % 27 < 27 := Nat.mod_lt y (by norm_num)
  have hq : (y % 27) / 9 < 3 :=
    (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by omega)
  interval_cases (y % 27) / 9 <;> omega

/-- The worst potential over the three possible child lifts modulo `27`. -/
def netHalfTargetPotentialMin (high : Bool) (r j : ℕ) : ℕ :=
  let b := oddBlockChildResidueBase r j
  min (netHalfStatePotential high b)
    (min (netHalfStatePotential high (b + 9))
      (netHalfStatePotential high (b + 18)))

/-- The adversarial three-lift minimum really is a lower bound for the
potential of every actual odd-block child. -/
theorem netHalfTargetPotentialMin_le_of_oddBlock {x y j : ℕ} (high : Bool)
    (h : 3 * y + 1 = 2 ^ j * x) :
    netHalfTargetPotentialMin high x j ≤ netHalfStatePotential high y := by
  rw [← netHalfStatePotential_mod_twentySeven high y]
  have h9 := oddBlockChild_mod_nine h
  have h27 := residue_mod_twentySeven_lifts h9
  dsimp [netHalfTargetPotentialMin]
  rcases h27 with h27 | h27 | h27
  · rw [h27]
    exact min_le_left _ _
  · rw [h27]
    exact (min_le_right _ _).trans (min_le_left _ _)
  · rw [h27]
    exact (min_le_right _ _).trans (min_le_right _ _)

/-- Whether this finite state may use the safe shrinking child. -/
def netHalfHasShrinkingChild (high : Bool) (r : ℕ) : Bool :=
  high && (r % 9 == 2 || r % 9 == 8)

theorem sevenCostsAt_mod_twentySeven (x : ℕ) :
    sevenCostsAt (x % 27) = sevenCostsAt x := by
  unfold sevenCostsAt
  rw [Nat.mod_mod_of_dvd x (by norm_num : 9 ∣ 27)]

theorem netHalfTargetPotentialMin_mod_twentySeven
    (high : Bool) (x j : ℕ) :
    netHalfTargetPotentialMin high (x % 27) j =
      netHalfTargetPotentialMin high x j := by
  simp [netHalfTargetPotentialMin, oddBlockChildResidueBase]

theorem netHalfHasShrinkingChild_mod_twentySeven (high : Bool) (x : ℕ) :
    netHalfHasShrinkingChild high (x % 27) =
      netHalfHasShrinkingChild high x := by
  simp [netHalfHasShrinkingChild,
    Nat.mod_mod_of_dvd x (by norm_num : 9 ∣ 27)]

/-- The rational under-approximation to the weighted one-generation image. -/
def netHalfImage (high : Bool) (r : ℕ) : ℚ :=
    (5 / 3 : ℚ) *
    (∑ i : Fin 7, (7 / 10 : ℚ) ^ sevenCostsAt r i *
        netHalfTargetPotentialMin
          (nextGrowingHeightState high (sevenCostsAt r i))
          r (sevenCostsAt r i) +
      if netHalfHasShrinkingChild high r then
        (7 / 10 : ℚ) * netHalfTargetPotentialMin false r 1
      else 0)

/-- The finite transfer image depends only on the source residue modulo `27`. -/
theorem netHalfImage_mod_twentySeven (high : Bool) (x : ℕ) :
    netHalfImage high (x % 27) = netHalfImage high x := by
  simp only [netHalfImage, sevenCostsAt_mod_twentySeven,
    netHalfTargetPotentialMin_mod_twentySeven,
    netHalfHasShrinkingChild_mod_twentySeven]

set_option maxHeartbeats 5000000 in
/-- Kernel-checked rational form of the net-height exponent-`1/2` certificate.
The true scale weight is `(3 / 2^j)^(1/2)`.  The checked rational weight
`(5/3) * (7/10)^j` is smaller because `(5/3)^2 < 3` and
`2 * (7/10)^2 < 1`. -/
theorem netHalfPotentialCertificate (high : Bool) (r : Fin 27)
    (hr : r.1 % 3 ≠ 0) :
    (netHalfStatePotential high r : ℚ) < netHalfImage high r := by
  cases high <;> fin_cases r <;> norm_num at hr <;>
    norm_num [netHalfStatePotential, lowPotential, highPotential, netHalfImage,
      sevenCostsAt, netHalfTargetPotentialMin, oddBlockChildResidueBase,
      nextGrowingHeightState, netHalfHasShrinkingChild, Fin.sum_univ_succ]

/-- The same finite certificate instantiated at an arbitrary reusable parent. -/
theorem netHalfPotentialCertificateAt (high : Bool) {x : ℕ} (h3 : ¬3 ∣ x) :
    (netHalfStatePotential high x : ℚ) < netHalfImage high x := by
  let r : Fin 27 := ⟨x % 27, Nat.mod_lt x (by norm_num)⟩
  have hx3 : x % 3 ≠ 0 := fun hx0 => h3 (Nat.dvd_of_mod_eq_zero hx0)
  have hr : r.1 % 3 ≠ 0 := by
    dsimp [r]
    rwa [Nat.mod_mod_of_dvd x (by norm_num : 3 ∣ 27)]
  have hcert := netHalfPotentialCertificate high r hr
  simpa [r, netHalfStatePotential_mod_twentySeven,
    netHalfImage_mod_twentySeven] using hcert

/-! ## Actual-child local expansion theorems -/

/-- When the finite state has no safe shrinking edge, the seven actual
growing children strictly expand the certified weighted potential. -/
theorem exists_netHalfGrowingExpansion {d x : ℕ} (high : Bool)
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InHeightState d high x)
    (hn : netHalfHasShrinkingChild high x = false) :
    ∃ ys : Fin 7 → ℕ, Function.Injective ys ∧
      (∀ i, GrowingUnitOddBlockChild x (ys i) (sevenCostsAt x i) ∧
        InHeightState d (nextGrowingHeightState high (sevenCostsAt x i)) (ys i)) ∧
      (netHalfStatePotential high x : ℚ) <
        (5 / 3 : ℚ) *
          ∑ i : Fin 7, (7 / 10 : ℚ) ^ sevenCostsAt x i *
            netHalfStatePotential
              (nextGrowingHeightState high (sevenCostsAt x i)) (ys i) := by
  obtain ⟨ys, hys, hchildren⟩ :=
    exists_exactSevenHeightChildren high hx h3 hstate
  have hcert := netHalfPotentialCertificateAt high h3
  simp [netHalfImage, hn] at hcert
  have htarget (i : Fin 7) :
      (netHalfTargetPotentialMin
          (nextGrowingHeightState high (sevenCostsAt x i))
          x (sevenCostsAt x i) : ℚ) ≤
        netHalfStatePotential
          (nextGrowingHeightState high (sevenCostsAt x i)) (ys i) := by
    exact_mod_cast netHalfTargetPotentialMin_le_of_oddBlock
      (nextGrowingHeightState high (sevenCostsAt x i))
      (hchildren i).1.2.2.2.2
  have hsum :
      (∑ i : Fin 7, (7 / 10 : ℚ) ^ sevenCostsAt x i *
        netHalfTargetPotentialMin
          (nextGrowingHeightState high (sevenCostsAt x i))
          x (sevenCostsAt x i)) ≤
      ∑ i : Fin 7, (7 / 10 : ℚ) ^ sevenCostsAt x i *
        netHalfStatePotential
          (nextGrowingHeightState high (sevenCostsAt x i)) (ys i) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (htarget i) (by positivity)
  exact ⟨ys, hys, hchildren,
    hcert.trans_le (mul_le_mul_of_nonneg_left hsum (by norm_num))⟩

/-- In a safe high source class, the seven actual growing children together
with the actual shrinking child strictly expand the certified potential. -/
theorem exists_netHalfShrinkingExpansion {d x : ℕ}
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InHeightState d true x)
    (hrem : x % 9 = 2 ∨ x % 9 = 8) :
    ∃ (ys : Fin 7 → ℕ) (z : ℕ), Function.Injective ys ∧
      (∀ i, GrowingUnitOddBlockChild x (ys i) (sevenCostsAt x i) ∧
        InHeightState d (nextGrowingHeightState true (sevenCostsAt x i)) (ys i)) ∧
      UnitOddBlockChildAtOne x z ∧ InHeightState d false z ∧
      (∀ i, z ≠ ys i) ∧
      (netHalfStatePotential true x : ℚ) <
        (5 / 3 : ℚ) *
          ((∑ i : Fin 7, (7 / 10 : ℚ) ^ sevenCostsAt x i *
            netHalfStatePotential
              (nextGrowingHeightState true (sevenCostsAt x i)) (ys i)) +
            (7 / 10 : ℚ) * netHalfStatePotential false z) := by
  obtain ⟨ys, hys, hchildren⟩ :=
    exists_exactSevenHeightChildren true hx h3 hstate
  obtain ⟨z, hz, hzstate⟩ := exists_shrinkingHeightChild hstate hrem
  have hdisjoint : ∀ i, z ≠ ys i := by
    intro i hzy
    have hzlt := hz.2.2.1
    have hxlt := (hchildren i).1.2.2.2.1
    omega
  have hhas : netHalfHasShrinkingChild true x = true := by
    rcases hrem with hrem | hrem <;>
      simp [netHalfHasShrinkingChild, hrem]
  have hcert := netHalfPotentialCertificateAt true h3
  simp [netHalfImage, hhas] at hcert
  have htarget (i : Fin 7) :
      (netHalfTargetPotentialMin
          (nextGrowingHeightState true (sevenCostsAt x i))
          x (sevenCostsAt x i) : ℚ) ≤
        netHalfStatePotential
          (nextGrowingHeightState true (sevenCostsAt x i)) (ys i) := by
    exact_mod_cast netHalfTargetPotentialMin_le_of_oddBlock
      (nextGrowingHeightState true (sevenCostsAt x i))
      (hchildren i).1.2.2.2.2
  have htargetOne :
      (netHalfTargetPotentialMin false x 1 : ℚ) ≤
        netHalfStatePotential false z := by
    exact_mod_cast netHalfTargetPotentialMin_le_of_oddBlock false
      (by simpa using hz.2.2.2)
  have hsum :
      (∑ i : Fin 7, (7 / 10 : ℚ) ^ sevenCostsAt x i *
        netHalfTargetPotentialMin
          (nextGrowingHeightState true (sevenCostsAt x i))
          x (sevenCostsAt x i)) ≤
      ∑ i : Fin 7, (7 / 10 : ℚ) ^ sevenCostsAt x i *
        netHalfStatePotential
          (nextGrowingHeightState true (sevenCostsAt x i)) (ys i) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (htarget i) (by positivity)
  have hinside :
      (∑ i : Fin 7, (7 / 10 : ℚ) ^ sevenCostsAt x i *
          netHalfTargetPotentialMin
            (nextGrowingHeightState true (sevenCostsAt x i))
            x (sevenCostsAt x i)) +
        (7 / 10 : ℚ) * netHalfTargetPotentialMin false x 1 ≤
      (∑ i : Fin 7, (7 / 10 : ℚ) ^ sevenCostsAt x i *
          netHalfStatePotential
            (nextGrowingHeightState true (sevenCostsAt x i)) (ys i)) +
        (7 / 10 : ℚ) * netHalfStatePotential false z :=
    add_le_add hsum (mul_le_mul_of_nonneg_left htargetOne (by norm_num))
  exact ⟨ys, z, hys, hchildren, hz, hzstate, hdisjoint,
    hcert.trans_le (mul_le_mul_of_nonneg_left hinside (by norm_num))⟩

/-- The two elementary rational under-estimates used above. -/
theorem netHalfRationalUnderestimate :
    (5 / 3 : ℚ) ^ 2 < 3 ∧ 2 * (7 / 10 : ℚ) ^ 2 < 1 := by
  norm_num

end CollatzMoonshot.FrontA
