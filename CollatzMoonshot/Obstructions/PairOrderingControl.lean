import CollatzMoonshot.Obstructions.PairDenominatorControl

/-!
# A primitive rational cycle with more than length-minus-one order inversions

This is a finite counterexample to equality in the general inversion lower
bound.  It is not an integer cycle or a general ordering theorem.
-/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

def pairOrderingCycle : List ℚ :=
  [28 / 23, 14 / 23, 7 / 23, 22 / 23, 11 / 23]

def pairOrderingSorted : List ℚ :=
  [7 / 23, 11 / 23, 14 / 23, 22 / 23, 28 / 23]

def pairOrderingImages : List ℚ :=
  pairOrderingSorted.map rationalShortcut

def pairOrderingInversions : ℕ :=
  (((Finset.range pairOrderingSorted.length).product
    (Finset.range pairOrderingSorted.length)).filter
      (fun ij => ij.1 < ij.2 ∧
        pairOrderingImages[ij.1]! > pairOrderingImages[ij.2]!)).card

/-- The sorted five states have six inversion pairs under the actual shortcut,
strictly more than the cycle length minus one. -/
theorem pair_ordering_control :
    pairOrderingCycle.map (fun x => (decide (0 < x), x.den)) =
      List.replicate 5 (true, 23) ∧
    pairOrderingCycle.Nodup ∧
    pairOrderingCycle.map rationalShortcut =
      [14 / 23, 7 / 23, 22 / 23, 11 / 23, 28 / 23] ∧
    pairOrderingSorted = [7 / 23, 11 / 23, 14 / 23, 22 / 23, 28 / 23] ∧
    pairOrderingImages = [22 / 23, 28 / 23, 7 / 23, 11 / 23, 14 / 23] ∧
    pairOrderingInversions = 6 ∧
    pairOrderingInversions > pairOrderingCycle.length - 1 := by
  native_decide

end CollatzMoonshot.Obstructions.ArithmeticLifts
