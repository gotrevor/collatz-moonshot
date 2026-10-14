/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindowThree.Finite

/-! Reverse-order pruning for the window-three cycle certificate. -/

namespace CollatzMoonshot.Amusical.WindowThreeFinite

def compatibleFiveOptions (twelve : List WindowConstraint) :
    List (List WindowConstraint) :=
  (pairConstraintOptions 5 4 (-4)).filter fun five =>
    decide (ConstraintsConsistent (five ++ twelve))

def compatibleTwoOptions (five twelve : List WindowConstraint) :
    List (List WindowConstraint) :=
  (pairConstraintOptions 2 2 (-2)).filter fun two =>
    decide (ConstraintsConsistent ((two ++ five) ++ twelve))

def compatibleFixedOptions (two five twelve : List WindowConstraint) :
    List (List WindowConstraint) :=
  fixedConstraintOptions.filter fun fixed =>
    decide (ConstraintsConsistent (combinedConstraints fixed two five twelve))

end CollatzMoonshot.Amusical.WindowThreeFinite
