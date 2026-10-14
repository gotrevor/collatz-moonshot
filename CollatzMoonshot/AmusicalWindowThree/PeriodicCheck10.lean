/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindowThree.PeriodicCheck9

/-! Shard 10 of the bounded period-at-most-twelve computation. -/

namespace CollatzMoonshot.Amusical.WindowThreePeriodic

set_option maxRecDepth 10000 in
theorem periodicBoundedCheck10 :
    ∀ y : ↥(Finset.Icc (1565 : ℤ) 1955), ∀ p : ↥(Finset.Icc 1 12),
      amusical^[p.1] y.1 = y.1 → |y.1| ∈ knownCycleMembers := by
  decide +kernel

end CollatzMoonshot.Amusical.WindowThreePeriodic
