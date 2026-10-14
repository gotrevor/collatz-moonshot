/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalRewireRatio.Schedule

/-! Exact successor transitions at canonical cut sources. -/

namespace CollatzMoonshot.Amusical

/-- Rewiring by a permutation of cut sources sends each indexed source to the target indexed by
its image.  This is the local bridge from cut combinatorics to the natural-number successor. -/
theorem scaleCut_rewired_apply (p : Equiv.Perm ScaleCutIndex) (i : ScaleCutIndex) :
    (amusicalNatPerm * scaleCutSourcePerm p) i.source = (p i).target := by
  rw [Equiv.Perm.mul_apply, scaleCutSourcePerm_apply, ScaleCutIndex.map_source]

namespace ScaleCutIndex

/-- At a nontrivial scheduled level, the base forward source enters the scheduled orbit through
its backward target. -/
theorem splice_rewired_baseForward (k b r : ℕ) (hbk : b ≤ k) (hrk : r ≤ k)
    (hb : IsInfiniteOrbitRep b) (hr : IsInfiniteOrbitRep r) (hbr : b ≠ r) :
    (amusicalNatPerm * scaleCutSourcePerm (spliceCycle k b r hbk hrk hb hr))
        (mkAt k b hbk hb .forward).source =
      (mkAt k r hrk hr .backward).target := by
  rw [scaleCut_rewired_apply, spliceCycle_apply_baseForward _ _ _ _ _ _ _ hbr]

/-- The scheduled orbit's backward source jumps to its forward target, crossing its central
segment in the successor chain. -/
theorem splice_rewired_repBackward (k b r : ℕ) (hbk : b ≤ k) (hrk : r ≤ k)
    (hb : IsInfiniteOrbitRep b) (hr : IsInfiniteOrbitRep r) (hbr : b ≠ r) :
    (amusicalNatPerm * scaleCutSourcePerm (spliceCycle k b r hbk hrk hb hr))
        (mkAt k r hrk hr .backward).source =
      (mkAt k r hrk hr .forward).target := by
  rw [scaleCut_rewired_apply, spliceCycle_apply_repBackward _ _ _ _ _ _ _ hbr]

/-- The scheduled orbit's forward source returns to the base orbit's forward target. -/
theorem splice_rewired_repForward (k b r : ℕ) (hbk : b ≤ k) (hrk : r ≤ k)
    (hb : IsInfiniteOrbitRep b) (hr : IsInfiniteOrbitRep r) (hbr : b ≠ r) :
    (amusicalNatPerm * scaleCutSourcePerm (spliceCycle k b r hbk hrk hb hr))
        (mkAt k r hrk hr .forward).source =
      (mkAt k b hbk hb .forward).target := by
  rw [scaleCut_rewired_apply, spliceCycle_apply_repForward _ _ _ _ _ _ _ hbr]

end ScaleCutIndex

end CollatzMoonshot.Amusical
