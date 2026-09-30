/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.MinimalRepairs

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

abbrev PairMove := List ℕ × List ℕ

def applyPairMove (s : List ℕ) (m : PairMove) : List ℕ := s.diff m.1 ++ m.2

def legalPairMove (s : List ℕ) (m : PairMove) : Bool :=
  decide ((m.1 : Multiset ℕ) ≤ (s : Multiset ℕ) ∧
    m.1.length = 2 ∧ m.2.length = 2 ∧
    (∀ u ∈ m.1 ++ m.2, 0 < u ∧ u % 2 = 1) ∧
    certificateValue 0 m.1 = certificateValue 0 m.2)

def legalPairMoves : List ℕ → List PairMove → Bool
  | _, [] => true
  | s, m :: ms => legalPairMove s m && legalPairMoves (applyPairMove s m) ms

def replayPairMoves (s : List ℕ) (ms : List PairMove) : List ℕ :=
  ms.foldl applyPairMove s

def unitEight : List ℕ := [19,25,29,55,83]
def unitThirteen : List ℕ := [5,7,7,11,17,55,65,83]

def sevenMoves : List PairMove :=
  [([35,53],[25,133]), ([65,133],[53,247]),
   ([17,53],[13,901]), ([247,901],[221,1577]),
   ([11,221],[13,55]), ([55,1577],[95,121]),
   ([13,95],[19,29]), ([7,121],[11,17])]

/-- Every step is an available positive-odd quadratic replacement.  The
endpoint is precisely the actual 7-path certificate plus the removable U8.
The powers of two are 4+5=9 initially and 6+3=9 finally. -/
theorem unit_assisted_quadratic_repair_seven :
    certificateValue 5 unitThirteen = 1 ∧ certificateValue 3 unitEight = 1 ∧
    legalPairMoves ([35,53] ++ unitThirteen) sevenMoves = true ∧
    (replayPairMoves ([35,53] ++ unitThirteen) sevenMoves : Multiset ℕ) =
      ([7,11,17,13,5] : List ℕ) + (unitEight : Multiset ℕ) ∧
    certificateValue 6 [7,11,17,13,5] = 7 := by
  native_decide

def catalystMoves : List PairMove :=
  [([7,121],[11,17]), ([65,133],[53,247]),
   ([17,53],[13,901]), ([247,901],[221,1577]),
   ([11,221],[13,55]), ([55,1577],[95,121]),
   ([13,95],[19,29])]

/-- The catalyst r121 returns unchanged; compare cubic_exchange_not_quadratic,
which forbids the same replacement in the three-factor context. -/
theorem explicit_quadratic_catalyst :
    legalPairMoves [7,65,133,121] catalystMoves = true ∧
    (replayPairMoves [7,65,133,121] catalystMoves : Multiset ℕ) =
      ([13,19,29,121] : List ℕ) := by
  native_decide

theorem essential_cubic_and_new_unit :
    certificateValue 0 [5,55,83] = certificateValue 0 [11,13,17] ∧
    certificateValue 5 [7,7,11,11,13,17,17,65] = 1 := by
  native_decide

end CollatzMoonshot.Obstructions.ArithmeticLifts
