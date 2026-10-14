/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindowThree.CycleCheckDef

/-! Kernel check of the reverse-pruned cycle certificate. -/

namespace CollatzMoonshot.Amusical.WindowThreeFinite

def cycleConstraintCheck : Bool :=
  (pairConstraintOptions 12 44 (-44)).all fun twelve =>
    (compatibleFiveOptions twelve).all fun five =>
      (compatibleTwoOptions five twelve).all fun two =>
        (compatibleFixedOptions two five twelve).all fun fixed =>
          decide (∃ i : Fin 24,
            ConstraintsEncodeRule (combinedConstraints fixed two five twelve) i)

set_option maxRecDepth 10000 in
theorem cycleConstraintCheck_eq_true : cycleConstraintCheck = true := by
  decide +kernel

end CollatzMoonshot.Amusical.WindowThreeFinite
