/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalRewireRatio.CutDynamics

/-! A levelwise sweep through every active infinite-orbit representative. -/

namespace CollatzMoonshot.Amusical

namespace ScaleCutIndex

/-- A non-base infinite representative active at level `k`. -/
def ActiveRepAt (b k : ℕ) :=
  {r : Fin (k + 1) // IsInfiniteOrbitRep r.1 ∧ r.1 ≠ b}

noncomputable instance activeRepAtFintype (b k : ℕ) : Fintype (ActiveRepAt b k) :=
  Fintype.ofInjective (fun r : ActiveRepAt b k => r.1) Subtype.val_injective

namespace ActiveRepAt

theorem isInfinite {b k : ℕ} (r : ActiveRepAt b k) : IsInfiniteOrbitRep r.1.1 :=
  r.2.1

theorem ne_base {b k : ℕ} (r : ActiveRepAt b k) : r.1.1 ≠ b :=
  r.2.2

theorem le_level {b k : ℕ} (r : ActiveRepAt b k) : r.1.1 ≤ k := by
  omega

end ActiveRepAt

/-- The finite list of all non-base infinite representatives active at one level. -/
noncomputable def activeReps (b k : ℕ) : List (ActiveRepAt b k) := by
  classical
  exact (Finset.univ : Finset (ActiveRepAt b k)).toList

@[simp] theorem mem_activeReps {b k : ℕ} (r : ActiveRepAt b k) :
    r ∈ activeReps b k := by
  classical
  simp [activeReps]

theorem activeReps_nodup (b k : ℕ) : (activeReps b k).Nodup := by
  classical
  exact Finset.nodup_toList _

/-- Cycle the base forward cut through the two cuts of every representative in a list. -/
noncomputable def sweepLocalAux (b k : ℕ) (hbk : b ≤ k) (hb : IsInfiniteOrbitRep b) :
    List (ActiveRepAt b k) → Equiv.Perm ScaleCutIndex
  | [] => 1
  | r :: rs =>
      sweepLocalAux b k hbk hb rs *
        spliceCycle k b r.1.1 hbk (by omega) hb r.2.1

theorem sweepLocalAux_level (b k : ℕ) (hbk : b ≤ k) (hb : IsInfiniteOrbitRep b)
    (rs : List (ActiveRepAt b k)) (i : ScaleCutIndex) :
    (sweepLocalAux b k hbk hb rs i).level = i.level := by
  induction rs generalizing i with
  | nil => rfl
  | cons r rs ih =>
      rw [sweepLocalAux, Equiv.Perm.mul_apply, ih]
      exact spliceCycle_level k b r.1.1 hbk (by omega) hb r.2.1 i

theorem spliceCycle_apply_of_ne (k b r : ℕ) (hbk : b ≤ k) (hrk : r ≤ k)
    (hb : IsInfiniteOrbitRep b) (hr : IsInfiniteOrbitRep r) (i : ScaleCutIndex)
    (hbase : i ≠ mkAt k b hbk hb .forward)
    (hback : i ≠ mkAt k r hrk hr .backward)
    (hfwd : i ≠ mkAt k r hrk hr .forward) :
    spliceCycle k b r hbk hrk hb hr i = i := by
  classical
  simp [spliceCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne,
    hbase, hback, hfwd]

theorem sweepLocalAux_apply_of_rep_not_mem (b k : ℕ) (hbk : b ≤ k)
    (hb : IsInfiniteOrbitRep b) (rs : List (ActiveRepAt b k)) (i : ScaleCutIndex)
    (hbase : i ≠ mkAt k b hbk hb .forward)
    (hrep : ∀ r ∈ rs, i.rep ≠ r.1.1) :
    sweepLocalAux b k hbk hb rs i = i := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      rw [sweepLocalAux, Equiv.Perm.mul_apply]
      have hr : i.rep ≠ r.1.1 := hrep r (by simp)
      have hfix : spliceCycle k b r.1.1 hbk r.le_level hb r.isInfinite i = i := by
        apply spliceCycle_apply_of_ne <;> intro heq
        · exact hbase heq
        · exact hr (congrArg ScaleCutIndex.rep heq)
        · exact hr (congrArg ScaleCutIndex.rep heq)
      rw [hfix]
      exact ih (fun s hs => hrep s (by simp [hs]))

theorem sweepLocalAux_apply_base_cons (b k : ℕ) (hbk : b ≤ k)
    (hb : IsInfiniteOrbitRep b) (r : ActiveRepAt b k) (rs : List (ActiveRepAt b k))
    (hnodup : (r :: rs).Nodup) :
    sweepLocalAux b k hbk hb (r :: rs) (mkAt k b hbk hb .forward) =
      mkAt k r.1.1 r.le_level r.isInfinite .backward := by
  rw [sweepLocalAux, Equiv.Perm.mul_apply,
    spliceCycle_apply_baseForward _ _ _ _ _ _ _ r.ne_base.symm]
  apply sweepLocalAux_apply_of_rep_not_mem
  · intro heq
    exact r.ne_base (congrArg ScaleCutIndex.rep heq)
  · intro s hs hrs
    have heq : r = s := by
      apply Subtype.ext
      apply Fin.ext
      exact hrs
    subst s
    exact hnodup.notMem hs

theorem sweepLocalAux_apply_backward (b k : ℕ) (hbk : b ≤ k)
    (hb : IsInfiniteOrbitRep b) (rs : List (ActiveRepAt b k)) (hnodup : rs.Nodup)
    (r : ActiveRepAt b k) (hr : r ∈ rs) :
    sweepLocalAux b k hbk hb rs (mkAt k r.1.1 r.le_level r.isInfinite .backward) =
      mkAt k r.1.1 r.le_level r.isInfinite .forward := by
  induction rs generalizing r with
  | nil => simp at hr
  | cons s rs ih =>
      by_cases hsr : s = r
      · subst s
        rw [sweepLocalAux, Equiv.Perm.mul_apply,
          spliceCycle_apply_repBackward _ _ _ _ _ _ _ r.ne_base.symm]
        apply sweepLocalAux_apply_of_rep_not_mem
        · intro heq
          exact r.ne_base (congrArg ScaleCutIndex.rep heq)
        · intro t ht hrt
          have heq : r = t := by
            apply Subtype.ext
            apply Fin.ext
            exact hrt
          subst t
          exact hnodup.notMem ht
      · rw [sweepLocalAux, Equiv.Perm.mul_apply]
        have hfix : spliceCycle k b s.1.1 hbk s.le_level hb s.isInfinite
            (mkAt k r.1.1 r.le_level r.isInfinite .backward) =
            mkAt k r.1.1 r.le_level r.isInfinite .backward := by
          apply spliceCycle_apply_of_ne <;> intro heq
          · exact r.ne_base (congrArg ScaleCutIndex.rep heq)
          · apply hsr
            apply Subtype.ext
            apply Fin.ext
            exact congrArg ScaleCutIndex.rep heq |>.symm
          · have hside := congrArg ScaleCutIndex.side heq
            exact ScaleCutSide.noConfusion hside
        rw [hfix]
        apply ih (r := r) hnodup.tail
        exact (List.mem_cons.mp hr).resolve_left (fun hrs => hsr hrs.symm)

theorem sweepLocalAux_apply_forward_singleton (b k : ℕ) (hbk : b ≤ k)
    (hb : IsInfiniteOrbitRep b) (r : ActiveRepAt b k) :
    sweepLocalAux b k hbk hb [r] (mkAt k r.1.1 r.le_level r.isInfinite .forward) =
      mkAt k b hbk hb .forward := by
  rw [sweepLocalAux, Equiv.Perm.mul_apply,
    spliceCycle_apply_repForward _ _ _ _ _ _ _ r.ne_base.symm]
  rfl

theorem sweepLocalAux_apply_forward_cons_cons (b k : ℕ) (hbk : b ≤ k)
    (hb : IsInfiniteOrbitRep b) (r s : ActiveRepAt b k)
    (rs : List (ActiveRepAt b k)) (hnodup : (r :: s :: rs).Nodup) :
    sweepLocalAux b k hbk hb (r :: s :: rs)
        (mkAt k r.1.1 r.le_level r.isInfinite .forward) =
      mkAt k s.1.1 s.le_level s.isInfinite .backward := by
  rw [sweepLocalAux, Equiv.Perm.mul_apply,
    spliceCycle_apply_repForward _ _ _ _ _ _ _ r.ne_base.symm]
  exact sweepLocalAux_apply_base_cons b k hbk hb s rs hnodup.tail

theorem sweepLocalAux_apply_forward_of_append_cons_cons (b k : ℕ) (hbk : b ≤ k)
    (hb : IsInfiniteOrbitRep b) (as : List (ActiveRepAt b k))
    (r s : ActiveRepAt b k) (rs : List (ActiveRepAt b k))
    (hnodup : (as ++ r :: s :: rs).Nodup) :
    sweepLocalAux b k hbk hb (as ++ r :: s :: rs)
        (mkAt k r.1.1 r.le_level r.isInfinite .forward) =
      mkAt k s.1.1 s.le_level s.isInfinite .backward := by
  induction as with
  | nil => exact sweepLocalAux_apply_forward_cons_cons b k hbk hb r s rs hnodup
  | cons t as ih =>
      rw [List.cons_append, sweepLocalAux, Equiv.Perm.mul_apply]
      have htr : t ≠ r := by
        intro heq
        subst t
        exact hnodup.notMem (by simp)
      have hfix : spliceCycle k b t.1.1 hbk t.le_level hb t.isInfinite
          (mkAt k r.1.1 r.le_level r.isInfinite .forward) =
          mkAt k r.1.1 r.le_level r.isInfinite .forward := by
        apply spliceCycle_apply_of_ne <;> intro heq
        · exact r.ne_base (congrArg ScaleCutIndex.rep heq)
        · have hside := congrArg ScaleCutIndex.side heq
          exact ScaleCutSide.noConfusion hside
        · apply htr
          apply Subtype.ext
          apply Fin.ext
          exact congrArg ScaleCutIndex.rep heq |>.symm
      rw [hfix]
      exact ih hnodup.tail

theorem sweepLocalAux_apply_forward_of_append_singleton (b k : ℕ) (hbk : b ≤ k)
    (hb : IsInfiniteOrbitRep b) (as : List (ActiveRepAt b k))
    (r : ActiveRepAt b k) (hnodup : (as ++ [r]).Nodup) :
    sweepLocalAux b k hbk hb (as ++ [r])
        (mkAt k r.1.1 r.le_level r.isInfinite .forward) =
      mkAt k b hbk hb .forward := by
  induction as with
  | nil => exact sweepLocalAux_apply_forward_singleton b k hbk hb r
  | cons t as ih =>
      rw [List.cons_append, sweepLocalAux, Equiv.Perm.mul_apply]
      have htr : t ≠ r := by
        intro heq
        subst t
        exact hnodup.notMem (by simp)
      have hfix : spliceCycle k b t.1.1 hbk t.le_level hb t.isInfinite
          (mkAt k r.1.1 r.le_level r.isInfinite .forward) =
          mkAt k r.1.1 r.le_level r.isInfinite .forward := by
        apply spliceCycle_apply_of_ne <;> intro heq
        · exact r.ne_base (congrArg ScaleCutIndex.rep heq)
        · have hside := congrArg ScaleCutIndex.side heq
          exact ScaleCutSide.noConfusion hside
        · apply htr
          apply Subtype.ext
          apply Fin.ext
          exact congrArg ScaleCutIndex.rep heq |>.symm
      rw [hfix]
      exact ih hnodup.tail

/-- The all-active local sweep, or the identity below the least representative. -/
noncomputable def sweepLocal (b k : ℕ) (hb : IsInfiniteOrbitRep b) :
    Equiv.Perm ScaleCutIndex := by
  classical
  exact if hbk : b ≤ k then sweepLocalAux b k hbk hb (activeReps b k) else 1

theorem sweepLocal_level (b k : ℕ) (hb : IsInfiniteOrbitRep b) (i : ScaleCutIndex) :
    (sweepLocal b k hb i).level = i.level := by
  classical
  unfold sweepLocal
  split
  · apply sweepLocalAux_level
  · rfl

/-- Assemble the all-active sweeps independently at every level. -/
noncomputable def sweepCutPerm (b : ℕ) (hb : IsInfiniteOrbitRep b) :
    Equiv.Perm ScaleCutIndex :=
  fiberwisePerm (sweepLocal b · hb) (sweepLocal_level b · hb)

theorem sweepCutPerm_level (b : ℕ) (hb : IsInfiniteOrbitRep b) (i : ScaleCutIndex) :
    (sweepCutPerm b hb i).level = i.level := by
  exact fiberwisePerm_level _ _ i

theorem sweepCutPerm_apply (b : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ r, IsInfiniteOrbitRep r → b ≤ r) (i : ScaleCutIndex) :
    sweepCutPerm b hb i =
      sweepLocalAux b i.level ((hbmin i.rep i.rep_isInfinite).trans i.rep_le) hb
        (activeReps b i.level) i := by
  classical
  rw [sweepCutPerm, fiberwisePerm_apply]
  unfold sweepLocal
  rw [dif_pos ((hbmin i.rep i.rep_isInfinite).trans i.rep_le)]

end ScaleCutIndex

end CollatzMoonshot.Amusical
