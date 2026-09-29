import CollatzMoonshot.Obstructions.ArithmeticLifts

/-!
# A rational shortcut cycle with a reduced pair gap denominator of seven

The eight cycle states all have reduced denominator 35.  The difference
between the last and third states is 15/7, so a denominator factor 5 does
not persist in every pair gap.  This is a finite certificate only.
-/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

/-- On odd-denominator rationals, numerator parity selects the shortcut step. -/
def rationalShortcut (x : ℚ) : ℚ :=
  if x.num % 2 = 0 then x / 2 else (3 * x + 1) / 2

def pairDenominatorCycle : List ℚ :=
  [208 / 35, 104 / 35, 52 / 35, 26 / 35,
   13 / 35, 37 / 35, 73 / 35, 127 / 35]

/-- Every displayed state is positive and has reduced denominator 35;
the list is distinct and the actual rational shortcut closes the cycle.
The last-minus-third gap reduces from 75/35 to 15/7. -/
theorem pair_denominator_control :
    pairDenominatorCycle.map (fun x => (decide (0 < x), x.den)) =
      List.replicate 8 (true, 35) ∧
    pairDenominatorCycle.Nodup ∧
    pairDenominatorCycle.map rationalShortcut =
      [104 / 35, 52 / 35, 26 / 35, 13 / 35,
       37 / 35, 73 / 35, 127 / 35, 208 / 35] ∧
    pairDenominatorCycle[7]! = (127 : ℚ) / 35 ∧
    pairDenominatorCycle[2]! = (52 : ℚ) / 35 ∧
    pairDenominatorCycle[7]! - pairDenominatorCycle[2]! = (15 : ℚ) / 7 ∧
    (pairDenominatorCycle[7]! - pairDenominatorCycle[2]!).den = 7 := by
  native_decide

end CollatzMoonshot.Obstructions.ArithmeticLifts
