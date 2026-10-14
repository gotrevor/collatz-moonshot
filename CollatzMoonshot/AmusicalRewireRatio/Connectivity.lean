/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalRewireRatio.Sweep

/-! Connectivity of the all-active sweep on canonical scale cuts. -/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

namespace ScaleCutIndex

/-- The induced successor on cut indices. -/
noncomputable def sweepCutSucc (b : ℕ) (hb : IsInfiniteOrbitRep b) :
    Equiv.Perm ScaleCutIndex :=
  orbitSucc * sweepCutPerm b hb

@[simp] theorem sweepCutSucc_apply (b : ℕ) (hb : IsInfiniteOrbitRep b)
    (i : ScaleCutIndex) :
    sweepCutSucc b hb i = orbitSucc (sweepCutPerm b hb i) := by
  rfl

theorem sameCycle_of_apply_eq {q : Equiv.Perm ScaleCutIndex} {i j : ScaleCutIndex}
    (hij : q i = j) : q.SameCycle i j := by
  refine ⟨1, ?_⟩
  simpa using hij

theorem sweepCutPerm_apply_backward (b k r : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (hr : IsInfiniteOrbitRep r)
    (hrb : r ≠ b) (hrk : r ≤ k) :
    sweepCutPerm b hb (mkAt k r hrk hr .backward) = mkAt k r hrk hr .forward := by
  let ar : ActiveRepAt b k := ⟨⟨r, by omega⟩, hr, hrb⟩
  rw [sweepCutPerm_apply b hb hbmin]
  simpa only [ar, mkAt] using
    sweepLocalAux_apply_backward b k ((hbmin r hr).trans hrk) hb
      (activeReps b k) (activeReps_nodup b k) ar (mem_activeReps ar)

theorem sweepCutPerm_apply_base_nil (b k : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (hbk : b ≤ k)
    (hlist : activeReps b k = []) :
    sweepCutPerm b hb (mkAt k b hbk hb .forward) = mkAt k b hbk hb .forward := by
  rw [sweepCutPerm_apply b hb hbmin]
  change sweepLocalAux b k ((hbmin b hb).trans hbk) hb (activeReps b k)
      (mkAt k b hbk hb .forward) = mkAt k b hbk hb .forward
  rw [hlist]
  rfl

theorem sweepCutPerm_apply_base_cons (b k : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (hbk : b ≤ k)
    (r : ActiveRepAt b k) (rs : List (ActiveRepAt b k))
    (hlist : activeReps b k = r :: rs) :
    sweepCutPerm b hb (mkAt k b hbk hb .forward) =
      mkAt k r.1.1 r.le_level r.isInfinite .backward := by
  rw [sweepCutPerm_apply b hb hbmin]
  change sweepLocalAux b k ((hbmin b hb).trans hbk) hb (activeReps b k)
      (mkAt k b hbk hb .forward) = mkAt k r.1.1 r.le_level r.isInfinite .backward
  rw [hlist]
  have hn := activeReps_nodup b k
  rw [hlist] at hn
  simpa only [mkAt] using sweepLocalAux_apply_base_cons b k
    ((hbmin b hb).trans hbk) hb r rs hn

theorem sweepCutPerm_apply_forward_next (b k : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ t, IsInfiniteOrbitRep t → b ≤ t) (hbk : b ≤ k)
    (as : List (ActiveRepAt b k)) (r s : ActiveRepAt b k)
    (rs : List (ActiveRepAt b k)) (hlist : activeReps b k = as ++ r :: s :: rs) :
    sweepCutPerm b hb (mkAt k r.1.1 r.le_level r.isInfinite .forward) =
      mkAt k s.1.1 s.le_level s.isInfinite .backward := by
  rw [sweepCutPerm_apply b hb hbmin]
  change sweepLocalAux b k ((hbmin r.1.1 r.isInfinite).trans r.le_level) hb
      (activeReps b k) (mkAt k r.1.1 r.le_level r.isInfinite .forward) =
        mkAt k s.1.1 s.le_level s.isInfinite .backward
  rw [hlist]
  have hn := activeReps_nodup b k
  rw [hlist] at hn
  simpa only [mkAt] using sweepLocalAux_apply_forward_of_append_cons_cons b k
    ((hbmin r.1.1 r.isInfinite).trans r.le_level) hb as r s rs hn

theorem sweepCutPerm_apply_forward_last (b k : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ t, IsInfiniteOrbitRep t → b ≤ t) (hbk : b ≤ k)
    (as : List (ActiveRepAt b k)) (r : ActiveRepAt b k)
    (hlist : activeReps b k = as ++ [r]) :
    sweepCutPerm b hb (mkAt k r.1.1 r.le_level r.isInfinite .forward) =
      mkAt k b hbk hb .forward := by
  rw [sweepCutPerm_apply b hb hbmin]
  change sweepLocalAux b k ((hbmin r.1.1 r.isInfinite).trans r.le_level) hb
      (activeReps b k) (mkAt k r.1.1 r.le_level r.isInfinite .forward) =
        mkAt k b hbk hb .forward
  rw [hlist]
  have hn := activeReps_nodup b k
  rw [hlist] at hn
  simpa only [mkAt] using sweepLocalAux_apply_forward_of_append_singleton b k
    ((hbmin r.1.1 r.isInfinite).trans r.le_level) hb as r hn

theorem sweepCutPerm_apply_baseBackward (b k : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (hbk : b ≤ k) :
    sweepCutPerm b hb (mkAt k b hbk hb .backward) = mkAt k b hbk hb .backward := by
  rw [sweepCutPerm_apply b hb hbmin]
  apply sweepLocalAux_apply_of_rep_not_mem
  · intro heq
    have hside := congrArg ScaleCutIndex.side heq
    exact ScaleCutSide.noConfusion hside
  · intro r _ hrep
    exact r.ne_base hrep.symm

/-- If the local sweep sends `x` to an active backward cut, the induced successor reaches the
matching forward cut in one step for a newly active representative and two steps otherwise. -/
theorem sweepCutSucc_sameCycle_to_activeForward (b k : ℕ)
    (hb : IsInfiniteOrbitRep b) (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s)
    (x : ScaleCutIndex) (r : ActiveRepAt b k)
    (hx : sweepCutPerm b hb x = mkAt k r.1.1 r.le_level r.isInfinite .backward) :
    (sweepCutSucc b hb).SameCycle x
      (mkAt k r.1.1 r.le_level r.isInfinite .forward) := by
  rcases lt_or_eq_of_le r.le_level with hrk | hrk
  · have hrprev : r.1.1 ≤ k - 1 := by omega
    let prev := mkAt (k - 1) r.1.1 hrprev r.isInfinite .backward
    have hfirst : sweepCutSucc b hb x = prev := by
      rw [sweepCutSucc_apply, hx,
        orbitSucc_apply_backward_of_lt (i := mkAt k r.1.1 r.le_level
          r.isInfinite .backward) rfl hrk]
      rfl
    have hsecond : sweepCutSucc b hb prev =
        mkAt k r.1.1 r.le_level r.isInfinite .forward := by
      rw [sweepCutSucc_apply, sweepCutPerm_apply_backward b (k - 1) r.1.1 hb hbmin
        r.isInfinite r.ne_base hrprev,
        orbitSucc_apply_forward (i := mkAt (k - 1) r.1.1 hrprev
          r.isInfinite .forward) rfl]
      simp only [prev, mkAt]
      congr 1 <;> omega
    exact (sameCycle_of_apply_eq hfirst).trans (sameCycle_of_apply_eq hsecond)
  · have hstep : sweepCutSucc b hb x =
        mkAt k r.1.1 r.le_level r.isInfinite .forward := by
      rw [sweepCutSucc_apply, hx,
        orbitSucc_apply_backward_of_eq (i := mkAt k r.1.1 r.le_level
          r.isInfinite .backward) rfl hrk]
      rfl
    exact sameCycle_of_apply_eq hstep

/-- From any active forward cut, the level sweep finishes at the base forward cut of the next
level. -/
theorem activeForward_sameCycle_nextBase (b k : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (r : ActiveRepAt b k) :
    (sweepCutSucc b hb).SameCycle
      (mkAt k r.1.1 r.le_level r.isInfinite .forward)
      (mkAt (k + 1) b ((hbmin r.1.1 r.isInfinite).trans (by omega)) hb .forward) := by
  let q := sweepCutSucc b hb
  have hbk : b ≤ k := (hbmin r.1.1 r.isInfinite).trans r.le_level
  have hrmem : r ∈ activeReps b k := mem_activeReps r
  obtain ⟨as, rs, hlist⟩ := List.append_of_mem hrmem
  have walk : ∀ (as : List (ActiveRepAt b k)) (r : ActiveRepAt b k)
      (rs : List (ActiveRepAt b k)), activeReps b k = as ++ r :: rs →
      q.SameCycle (mkAt k r.1.1 r.le_level r.isInfinite .forward)
        (mkAt (k + 1) b (hbk.trans (by omega)) hb .forward) := by
    intro as r rs hlist
    induction rs generalizing as r with
    | nil =>
        have hp := sweepCutPerm_apply_forward_last b k hb hbmin hbk as r (by
          simpa using hlist)
        apply sameCycle_of_apply_eq
        rw [sweepCutSucc_apply, hp,
          orbitSucc_apply_forward (i := mkAt k b hbk hb .forward) rfl]
        rfl
    | cons s rs ih =>
        have hp := sweepCutPerm_apply_forward_next b k hb hbmin hbk as r s rs hlist
        apply (sweepCutSucc_sameCycle_to_activeForward b k hb hbmin
          (mkAt k r.1.1 r.le_level r.isInfinite .forward) s hp).trans
        apply ih (as := as ++ [r]) (r := s)
        exact hlist.trans (List.append_assoc as [r] (s :: rs)).symm
  exact walk as r rs hlist

theorem baseForward_sameCycle_succ (b k : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (hbk : b ≤ k) :
    (sweepCutSucc b hb).SameCycle (mkAt k b hbk hb .forward)
      (mkAt (k + 1) b (hbk.trans (by omega)) hb .forward) := by
  cases hlist : activeReps b k with
  | nil =>
      have hp := sweepCutPerm_apply_base_nil b k hb hbmin hbk hlist
      apply sameCycle_of_apply_eq
      rw [sweepCutSucc_apply, hp,
        orbitSucc_apply_forward (i := mkAt k b hbk hb .forward) rfl]
      rfl
  | cons r rs =>
      have hp := sweepCutPerm_apply_base_cons b k hb hbmin hbk r rs hlist
      exact (sweepCutSucc_sameCycle_to_activeForward b k hb hbmin
        (mkAt k b hbk hb .forward) r hp).trans
          (activeForward_sameCycle_nextBase b k hb hbmin r)

theorem baseForward_sameCycle_add (b : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (d : ℕ) :
    (sweepCutSucc b hb).SameCycle (mkAt b b le_rfl hb .forward)
      (mkAt (b + d) b (Nat.le_add_right b d) hb .forward) := by
  induction d with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ d ih =>
      exact ih.trans (baseForward_sameCycle_succ b (b + d) hb hbmin
        (Nat.le_add_right b d))

theorem baseForward_sameCycle (b k : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (hbk : b ≤ k) :
    (sweepCutSucc b hb).SameCycle (mkAt b b le_rfl hb .forward)
      (mkAt k b hbk hb .forward) := by
  simpa only [Nat.add_sub_of_le hbk, mkAt] using
    baseForward_sameCycle_add b hb hbmin (k - b)

theorem baseBackward_sameCycle_add (b : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (d : ℕ) :
    (sweepCutSucc b hb).SameCycle
      (mkAt (b + d) b (Nat.le_add_right b d) hb .backward)
      (mkAt b b le_rfl hb .forward) := by
  induction d with
  | zero =>
      have hp := sweepCutPerm_apply_baseBackward b b hb hbmin le_rfl
      have hstep : sweepCutSucc b hb (mkAt b b le_rfl hb .backward) =
          mkAt b b le_rfl hb .forward := by
        rw [sweepCutSucc_apply, hp,
          orbitSucc_apply_backward_of_eq (i := mkAt b b le_rfl hb .backward) rfl rfl]
        rfl
      simpa only [Nat.add_zero, mkAt] using sameCycle_of_apply_eq hstep
  | succ d ih =>
      have hlevel : b < b + (d + 1) := by omega
      have hp := sweepCutPerm_apply_baseBackward b (b + (d + 1)) hb hbmin (by omega)
      have hstep : (sweepCutSucc b hb).SameCycle
          (mkAt (b + (d + 1)) b (by omega) hb .backward)
          (mkAt (b + d) b (by omega) hb .backward) := by
        apply sameCycle_of_apply_eq
        rw [sweepCutSucc_apply, hp,
          orbitSucc_apply_backward_of_lt
            (i := mkAt (b + (d + 1)) b (by omega) hb .backward) rfl hlevel]
        simp only [mkAt]
        congr 1 <;> omega
      exact hstep.trans ih

theorem base_sameCycle_forward (b k r : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (hr : IsInfiniteOrbitRep r)
    (hrk : r ≤ k) :
    (sweepCutSucc b hb).SameCycle (mkAt b b le_rfl hb .forward)
      (mkAt k r hrk hr .forward) := by
  by_cases hrb : r = b
  · subst r
    exact baseForward_sameCycle b k hb hbmin hrk
  · let ar : ActiveRepAt b k := ⟨⟨r, by omega⟩, hr, hrb⟩
    have hbase := baseForward_sameCycle b k hb hbmin ((hbmin r hr).trans hrk)
    have hstep := baseForward_sameCycle_succ b k hb hbmin ((hbmin r hr).trans hrk)
    have htail := activeForward_sameCycle_nextBase b k hb hbmin ar
    exact hbase.trans (hstep.trans (by simpa only [ar, mkAt] using htail.symm))

theorem base_sameCycle_backward (b k r : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (hr : IsInfiniteOrbitRep r)
    (hrk : r ≤ k) :
    (sweepCutSucc b hb).SameCycle (mkAt b b le_rfl hb .forward)
      (mkAt k r hrk hr .backward) := by
  by_cases hrb : r = b
  · subst r
    have hback := baseBackward_sameCycle_add b hb hbmin (k - b)
    simpa only [Nat.add_sub_of_le hrk, mkAt] using hback.symm
  · have hforward := base_sameCycle_forward b (k + 1) r hb hbmin hr (by omega)
    have hp := sweepCutPerm_apply_backward b k r hb hbmin hr hrb hrk
    have hstep : (sweepCutSucc b hb).SameCycle (mkAt k r hrk hr .backward)
        (mkAt (k + 1) r (by omega) hr .forward) := by
      apply sameCycle_of_apply_eq
      rw [sweepCutSucc_apply, hp,
        orbitSucc_apply_forward (i := mkAt k r hrk hr .forward) rfl]
      rfl
    exact hforward.trans hstep.symm

theorem base_sameCycle_index (b : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (i : ScaleCutIndex) :
    (sweepCutSucc b hb).SameCycle (mkAt b b le_rfl hb .forward) i := by
  cases i with
  | mk level rep rep_le rep_isInfinite side =>
      cases side with
      | backward => exact base_sameCycle_backward b level rep hb hbmin rep_isInfinite rep_le
      | forward => exact base_sameCycle_forward b level rep hb hbmin rep_isInfinite rep_le

theorem sweepCutSucc_sameCycle (b : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (i j : ScaleCutIndex) :
    (sweepCutSucc b hb).SameCycle i j :=
  (base_sameCycle_index b hb hbmin i).symm.trans (base_sameCycle_index b hb hbmin j)

/-- Each induced cut transition is realized by a positive number of steps of the rewired natural
permutation. -/
theorem sweepRewired_sameCycle_cutSucc (b : ℕ) (hb : IsInfiniteOrbitRep b)
    (i : ScaleCutIndex) :
    (amusicalNatPerm * scaleCutSourcePerm (sweepCutPerm b hb)).SameCycle i.source
      (sweepCutSucc b hb i).source := by
  refine ⟨((sweepCutPerm b hb i).orbitSegmentLength : ℤ), ?_⟩
  exact rewired_zpow_orbitSegmentLength_source (sweepCutPerm b hb) i

theorem sweepRewired_sameCycle_cutSucc_zpow (b : ℕ) (hb : IsInfiniteOrbitRep b)
    (j : ℤ) (i : ScaleCutIndex) :
    (amusicalNatPerm * scaleCutSourcePerm (sweepCutPerm b hb)).SameCycle i.source
      ((sweepCutSucc b hb ^ j) i).source := by
  induction j using Int.induction_on with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ j ih =>
      apply ih.trans
      have h := sweepRewired_sameCycle_cutSucc b hb ((sweepCutSucc b hb ^ (j : ℤ)) i)
      have heq : sweepCutSucc b hb ((sweepCutSucc b hb ^ (j : ℤ)) i) =
          (sweepCutSucc b hb ^ ((j : ℤ) + 1)) i := by
        calc
          _ = ((sweepCutSucc b hb ^ (1 : ℤ)) *
              (sweepCutSucc b hb ^ (j : ℤ))) i := by
            rw [zpow_one, Equiv.Perm.mul_apply]
          _ = (sweepCutSucc b hb ^ ((1 : ℤ) + j)) i := by rw [zpow_add]
          _ = (sweepCutSucc b hb ^ ((j : ℤ) + 1)) i := by
            congr 2
            omega
      rwa [heq] at h
  | pred j ih =>
      apply ih.trans
      have h := sweepRewired_sameCycle_cutSucc b hb
        ((sweepCutSucc b hb ^ (-(j : ℤ) - 1)) i)
      have heq : sweepCutSucc b hb ((sweepCutSucc b hb ^ (-(j : ℤ) - 1)) i) =
          (sweepCutSucc b hb ^ (-(j : ℤ))) i := by
        calc
          _ = ((sweepCutSucc b hb ^ (1 : ℤ)) *
              (sweepCutSucc b hb ^ (-(j : ℤ) - 1))) i := by
            rw [zpow_one, Equiv.Perm.mul_apply]
          _ = (sweepCutSucc b hb ^ ((1 : ℤ) + (-(j : ℤ) - 1))) i := by
            rw [zpow_add]
          _ = (sweepCutSucc b hb ^ (-(j : ℤ))) i := by
            congr 2
            omega
      rw [heq] at h
      exact h.symm

theorem sweepRewired_sameCycle_cutSources (b : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (i j : ScaleCutIndex) :
    (amusicalNatPerm * scaleCutSourcePerm (sweepCutPerm b hb)).SameCycle
      i.source j.source := by
  obtain ⟨n, hn⟩ := sweepCutSucc_sameCycle b hb hbmin i j
  have h := sweepRewired_sameCycle_cutSucc_zpow b hb n i
  rwa [hn] at h

end ScaleCutIndex

theorem level_sub_rep_lt_forwardPassage {r k : ℕ} (hr : IsInfiniteOrbitRep r)
    (hrk : r ≤ k) :
    k - r < forwardPassage hr.2 (scaleCutBase k) := by
  let f : ℕ → ℕ := fun d => forwardPassage hr.2 (scaleCutBase (r + d))
  have hf : StrictMono f := by
    intro a c hac
    exact forwardPassage_strictMono_scaleCutBase hr (by omega) (by omega)
  have hle := hf.add_le_nat (k - r) 0
  have hpos := forwardPassage_pos hr.2 (scaleCutBase r)
    (level_le_scaleCutBase r)
  simp only [f, Nat.add_zero, Nat.add_sub_of_le hrk] at hle
  omega

theorem exists_forward_scaleCutSource {n : ℕ} (hn : (amusicalOrbit (n : ℤ)).Infinite) :
    ∃ t : ℕ, (amusicalNatPerm ^ (t : ℤ)) n ∈ Set.range ScaleCutIndex.source := by
  let r := orbitMinNat (n : ℤ)
  have hr : IsInfiniteOrbitRep r := orbitMinNat_isInfiniteOrbitRep hn
  have hrmem : (r : ℤ) ∈ amusicalOrbit (n : ℤ) := orbitMinNat_mem (Int.natCast_nonneg n)
  have hrorbit : amusicalOrbit (r : ℤ) = amusicalOrbit (n : ℤ) :=
    amusicalOrbit_eq_of_mem hrmem
  have hnmem : (n : ℤ) ∈ amusicalOrbit (r : ℤ) := by
    rw [hrorbit]
    exact mem_amusicalOrbit_self n
  obtain ⟨j, hj⟩ := hnmem
  have hjnat : (amusicalNatPerm ^ j) r = n := by
    apply Nat.cast_injective (R := ℤ)
    rw [amusicalNatPerm_zpow_apply_cast]
    exact hj
  let k := r + j.natAbs + 1
  have hrk : r ≤ k := by omega
  let i := ScaleCutIndex.mkAt k r hrk hr .forward
  have hpass := level_sub_rep_lt_forwardPassage hr hrk
  have hjle : j ≤ i.cutTime := by
    have hjabs : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
    simp only [ScaleCutIndex.cutTime, i, ScaleCutIndex.mkAt]
    push_cast
    dsimp only [k] at hpass ⊢
    omega
  let d := (i.cutTime - j).toNat
  have hnonneg : 0 ≤ i.cutTime - j := sub_nonneg.mpr hjle
  have hd : (d : ℤ) = i.cutTime - j := by
    exact Int.toNat_of_nonneg hnonneg
  have htime : i.cutTime = (d : ℤ) + j := by omega
  refine ⟨d, i, ?_⟩
  calc
    i.source = (amusicalNatPerm ^ i.cutTime) r := i.source_eq_zpow_cutTime
    _ = (amusicalNatPerm ^ ((d : ℤ) + j)) r := by rw [htime]
    _ = (amusicalNatPerm ^ (d : ℤ)) ((amusicalNatPerm ^ j) r) := by
      rw [zpow_add, Equiv.Perm.mul_apply]
    _ = (amusicalNatPerm ^ (d : ℤ)) n := by rw [hjnat]

/-- Before the first canonical cut source on its original forward orbit, a point follows the
same path under every scale-cut rewiring. -/
theorem rewired_sameCycle_first_scaleCutSource (p : Equiv.Perm ScaleCutIndex) {n : ℕ}
    (hn : (amusicalOrbit (n : ℤ)).Infinite) :
    ∃ i : ScaleCutIndex,
      (amusicalNatPerm * scaleCutSourcePerm p).SameCycle n i.source := by
  classical
  let t := Nat.find (exists_forward_scaleCutSource hn)
  have ht := Nat.find_spec (exists_forward_scaleCutSource hn)
  obtain ⟨i, hi⟩ := ht
  refine ⟨i, t, ?_⟩
  have hpath : ∀ s ≤ t,
      ((amusicalNatPerm * scaleCutSourcePerm p) ^ (s : ℤ)) n =
        (amusicalNatPerm ^ (s : ℤ)) n := by
    intro s hs
    induction s with
    | zero => rfl
    | succ s ih =>
        have hslt : s < t := by omega
        have hnot : (amusicalNatPerm ^ (s : ℤ)) n ∉
            Set.range ScaleCutIndex.source := by
          intro hmem
          have hle := Nat.find_min' (exists_forward_scaleCutSource hn) hmem
          omega
        rw [show ((s + 1 : ℕ) : ℤ) = 1 + (s : ℤ) by omega]
        rw [zpow_add, zpow_add, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          zpow_one, zpow_one, ih (by omega), Equiv.Perm.mul_apply,
          scaleCutSourcePerm_apply_of_not_range p hnot]
  rw [hpath t le_rfl]
  exact hi.symm

/-- The all-active sweep connects every point lying on an infinite nonnegative orbit. -/
theorem sweepRewired_connected (b : ℕ) (hb : IsInfiniteOrbitRep b)
    (hbmin : ∀ s, IsInfiniteOrbitRep s → b ≤ s) (a c : ℕ)
    (ha : (amusicalOrbit (a : ℤ)).Infinite)
    (hc : (amusicalOrbit (c : ℤ)).Infinite) :
    ∃ j : ℤ,
      ((amusicalNatPerm * scaleCutSourcePerm (ScaleCutIndex.sweepCutPerm b hb)) ^ j) a = c := by
  obtain ⟨i, hi⟩ := rewired_sameCycle_first_scaleCutSource
    (ScaleCutIndex.sweepCutPerm b hb) ha
  obtain ⟨k, hk⟩ := rewired_sameCycle_first_scaleCutSource
    (ScaleCutIndex.sweepCutPerm b hb) hc
  exact hi.trans (ScaleCutIndex.sweepRewired_sameCycle_cutSources b hb hbmin i k) |>.trans hk.symm

end CollatzMoonshot.Amusical
