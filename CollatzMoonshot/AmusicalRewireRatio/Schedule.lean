/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalRewireRatio.Cuts

/-! Levelwise permutations and the elementary three-cut splice used by the global schedule. -/

namespace CollatzMoonshot.Amusical

namespace ScaleCutIndex

/-- Apply a separate permutation on every level.  The preservation hypothesis makes the
pointwise inverse use the same member of the family. -/
noncomputable def fiberwisePerm (q : ℕ → Equiv.Perm ScaleCutIndex)
    (hq : ∀ k i, (q k i).level = i.level) : Equiv.Perm ScaleCutIndex where
  toFun i := q i.level i
  invFun i := (q i.level).symm i
  left_inv i := by
    have hforward : (q i.level i).level = i.level := hq i.level i
    change (q (q i.level i).level).symm (q i.level i) = i
    rw [hforward]
    exact (q i.level).symm_apply_apply i
  right_inv i := by
    change q ((q i.level).symm i).level ((q i.level).symm i) = i
    rw [show ((q i.level).symm i).level = i.level by
      have h := hq i.level ((q i.level).symm i)
      simpa using h.symm]
    exact (q i.level).apply_symm_apply i

theorem fiberwisePerm_apply (q : ℕ → Equiv.Perm ScaleCutIndex)
    (hq : ∀ k i, (q k i).level = i.level) (i : ScaleCutIndex) :
    fiberwisePerm q hq i = q i.level i := by
  rfl

theorem fiberwisePerm_level (q : ℕ → Equiv.Perm ScaleCutIndex)
    (hq : ∀ k i, (q k i).level = i.level) (i : ScaleCutIndex) :
    (fiberwisePerm q hq i).level = i.level := by
  rw [fiberwisePerm_apply]
  exact hq i.level i

/-- The cut on a specified side of an active representative. -/
def mkAt (k r : ℕ) (hrk : r ≤ k) (hr : IsInfiniteOrbitRep r)
    (side : ScaleCutSide) : ScaleCutIndex :=
  ⟨k, r, hrk, hr, side⟩

theorem mkAt_level (k r : ℕ) (hrk : r ≤ k) (hr : IsInfiniteOrbitRep r)
    (side : ScaleCutSide) : (mkAt k r hrk hr side).level = k := by
  rfl

/-- At one level, insert orbit `r` into the base orbit by cycling its backward and forward cuts
with the base forward cut.  The orientation is chosen later by the connectivity proof. -/
noncomputable def spliceCycle (k b r : ℕ) (hbk : b ≤ k) (hrk : r ≤ k)
    (hb : IsInfiniteOrbitRep b) (hr : IsInfiniteOrbitRep r) :
    Equiv.Perm ScaleCutIndex := by
  classical
  exact Equiv.swap (mkAt k b hbk hb .forward) (mkAt k r hrk hr .backward) *
    Equiv.swap (mkAt k r hrk hr .backward) (mkAt k r hrk hr .forward)

theorem swap_level_of_eq [DecidableEq ScaleCutIndex] {a b : ScaleCutIndex}
    (hab : a.level = b.level)
    (i : ScaleCutIndex) : (Equiv.swap a b i).level = i.level := by
  by_cases hia : i = a
  · subst i
    simp [hab]
  by_cases hib : i = b
  · subst i
    simp [hab]
  rw [Equiv.swap_apply_of_ne_of_ne hia hib]

theorem spliceCycle_level (k b r : ℕ) (hbk : b ≤ k) (hrk : r ≤ k)
    (hb : IsInfiniteOrbitRep b) (hr : IsInfiniteOrbitRep r) (i : ScaleCutIndex) :
    (spliceCycle k b r hbk hrk hb hr i).level = i.level := by
  classical
  unfold spliceCycle
  rw [Equiv.Perm.mul_apply]
  apply (swap_level_of_eq (a := mkAt k b hbk hb .forward)
    (b := mkAt k r hrk hr .backward) (by rfl) _).trans
  exact swap_level_of_eq (a := mkAt k r hrk hr .backward)
    (b := mkAt k r hrk hr .forward) (by rfl) i

theorem spliceCycle_apply_baseForward (k b r : ℕ) (hbk : b ≤ k) (hrk : r ≤ k)
    (hb : IsInfiniteOrbitRep b) (hr : IsInfiniteOrbitRep r) (hbr : b ≠ r) :
    spliceCycle k b r hbk hrk hb hr (mkAt k b hbk hb .forward) =
      mkAt k r hrk hr .backward := by
  classical
  simp only [spliceCycle, Equiv.Perm.mul_apply]
  have hab : mkAt k b hbk hb .forward ≠ mkAt k r hrk hr .backward := by
    intro h
    exact hbr (congrArg ScaleCutIndex.rep h)
  have hac : mkAt k b hbk hb .forward ≠ mkAt k r hrk hr .forward := by
    intro h
    exact hbr (congrArg ScaleCutIndex.rep h)
  rw [Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]

theorem spliceCycle_apply_repBackward (k b r : ℕ) (hbk : b ≤ k) (hrk : r ≤ k)
    (hb : IsInfiniteOrbitRep b) (hr : IsInfiniteOrbitRep r) (hbr : b ≠ r) :
    spliceCycle k b r hbk hrk hb hr (mkAt k r hrk hr .backward) =
      mkAt k r hrk hr .forward := by
  classical
  simp only [spliceCycle, Equiv.Perm.mul_apply]
  have hca : mkAt k r hrk hr .forward ≠ mkAt k b hbk hb .forward := by
    intro h
    exact hbr (congrArg ScaleCutIndex.rep h).symm
  have hcb : mkAt k r hrk hr .forward ≠ mkAt k r hrk hr .backward := by
    intro h
    have := congrArg ScaleCutIndex.side h
    exact ScaleCutSide.noConfusion this
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcb]

theorem spliceCycle_apply_repForward (k b r : ℕ) (hbk : b ≤ k) (hrk : r ≤ k)
    (hb : IsInfiniteOrbitRep b) (hr : IsInfiniteOrbitRep r) (_hbr : b ≠ r) :
    spliceCycle k b r hbk hrk hb hr (mkAt k r hrk hr .forward) =
      mkAt k b hbk hb .forward := by
  classical
  simp only [spliceCycle, Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_right, Equiv.swap_apply_right]

/-- At level `k`, schedule the representative in the left coordinate of `unpair k`.  Invalid
coordinates and the base representative give the identity. -/
noncomputable def scheduledLocal (b k : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ r, IsInfiniteOrbitRep r → b ≤ r) : Equiv.Perm ScaleCutIndex := by
  classical
  let r := (Nat.unpair k).1
  exact if hr : IsInfiniteOrbitRep r ∧ r ≠ b then
    spliceCycle k b r ((hbmin r hr.1).trans (Nat.unpair_left_le k))
      (Nat.unpair_left_le k) hb hr.1
  else 1

theorem scheduledLocal_level (b k : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ r, IsInfiniteOrbitRep r → b ≤ r) (i : ScaleCutIndex) :
    (scheduledLocal b k hb hbmin i).level = i.level := by
  classical
  unfold scheduledLocal
  dsimp only
  split
  · apply spliceCycle_level
  · rfl

/-- The global cut permutation obtained by applying the scheduled three-cycle independently on
each level.  Every representative distinct from `b` is scheduled at all levels `pair r t`. -/
noncomputable def scheduledCutPerm (b : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ r, IsInfiniteOrbitRep r → b ≤ r) : Equiv.Perm ScaleCutIndex :=
  fiberwisePerm (scheduledLocal b · hb hbmin) (scheduledLocal_level b · hb hbmin)

theorem scheduledCutPerm_level (b : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ r, IsInfiniteOrbitRep r → b ≤ r) (i : ScaleCutIndex) :
    (scheduledCutPerm b hb hbmin i).level = i.level := by
  exact fiberwisePerm_level _ _ i

end ScaleCutIndex

end CollatzMoonshot.Amusical
