/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindowThree.PeriodicCheck11

/-! Assembly of the twelve bounded-period computation shards. -/

namespace CollatzMoonshot.Amusical.WindowThreePeriodic

set_option maxRecDepth 10000 in
theorem periodicBoundedCheck :
    ∀ y : ↥(Finset.Icc (-2346 : ℤ) 2346), ∀ p : ↥(Finset.Icc 1 12),
      amusical^[p.1] y.1 = y.1 → |y.1| ∈ knownCycleMembers := by
  intro y p hperiod
  have hy := Finset.mem_Icc.mp y.property
  by_cases h0 : y.1 ≤ -1956
  · exact periodicBoundedCheck0
      ⟨y.1, Finset.mem_Icc.mpr ⟨hy.1, h0⟩⟩ p hperiod
  · by_cases h1 : y.1 ≤ -1565
    · exact periodicBoundedCheck1
        ⟨y.1, Finset.mem_Icc.mpr ⟨by omega, h1⟩⟩ p hperiod
    · by_cases h2 : y.1 ≤ -1174
      · exact periodicBoundedCheck2
          ⟨y.1, Finset.mem_Icc.mpr ⟨by omega, h2⟩⟩ p hperiod
      · by_cases h3 : y.1 ≤ -783
        · exact periodicBoundedCheck3
            ⟨y.1, Finset.mem_Icc.mpr ⟨by omega, h3⟩⟩ p hperiod
        · by_cases h4 : y.1 ≤ -392
          · exact periodicBoundedCheck4
              ⟨y.1, Finset.mem_Icc.mpr ⟨by omega, h4⟩⟩ p hperiod
          · by_cases h5 : y.1 ≤ -1
            · exact periodicBoundedCheck5
                ⟨y.1, Finset.mem_Icc.mpr ⟨by omega, h5⟩⟩ p hperiod
            · by_cases h6 : y.1 ≤ 390
              · exact periodicBoundedCheck6
                  ⟨y.1, Finset.mem_Icc.mpr ⟨by omega, h6⟩⟩ p hperiod
              · by_cases h7 : y.1 ≤ 782
                · exact periodicBoundedCheck7
                    ⟨y.1, Finset.mem_Icc.mpr ⟨by omega, h7⟩⟩ p hperiod
                · by_cases h8 : y.1 ≤ 1173
                  · exact periodicBoundedCheck8
                      ⟨y.1, Finset.mem_Icc.mpr ⟨by omega, h8⟩⟩ p hperiod
                  · by_cases h9 : y.1 ≤ 1564
                    · exact periodicBoundedCheck9
                        ⟨y.1, Finset.mem_Icc.mpr ⟨by omega, h9⟩⟩ p hperiod
                    · by_cases h10 : y.1 ≤ 1955
                      · exact periodicBoundedCheck10
                          ⟨y.1, Finset.mem_Icc.mpr ⟨by omega, h10⟩⟩ p hperiod
                      · exact periodicBoundedCheck11
                          ⟨y.1, Finset.mem_Icc.mpr ⟨by omega, hy.2⟩⟩ p hperiod

end CollatzMoonshot.Amusical.WindowThreePeriodic
