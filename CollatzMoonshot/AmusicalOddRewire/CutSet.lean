/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalSeventh.Rewire

/-!
# Reconnecting a permutation of `ℕ` along an arbitrary cut set

The construction behind `rewire_single_orbit` (`AmusicalSeventh/Rewire.lean`) with the cut set as a
parameter.  A set `C` is a cut set for `σ` when it is infinite and every cut has a later and an
earlier cut on its `σ`-orbit.  The cuts split the orbits through `C` into finite segments;
`IsCutSet.glue` strings all segments into one orbit.  It differs from `σ` only at points `n`
with `σ n ∈ C`, and every point whose forward orbit reaches `C` lies on the one glued orbit.
-/

namespace CollatzMoonshot.Amusical

/-- `C` is an infinite set of cut points, each with a later and an earlier cut on its orbit. -/
structure IsCutSet (σ : Equiv.Perm ℕ) (C : Set ℕ) : Prop where
  next : ∀ c ∈ C, ∃ k : ℕ, 0 < k ∧ (σ ^ (k : ℤ)) c ∈ C
  prev : ∀ c ∈ C, ∃ k : ℕ, 0 < k ∧ (σ ^ (-(k : ℤ))) c ∈ C
  infinite : C.Infinite

namespace IsCutSet

variable {σ : Equiv.Perm ℕ} {C : Set ℕ}

/-- The first positive time at which the orbit of a cut reaches another cut. -/
noncomputable def nextTime (hC : IsCutSet σ C) (c : C) : ℕ := by
  classical
  exact Nat.find (hC.next c c.2)

theorem nextTime_spec (hC : IsCutSet σ C) (c : C) :
    0 < hC.nextTime c ∧ (σ ^ (hC.nextTime c : ℤ)) (c : ℕ) ∈ C := by
  classical
  exact Nat.find_spec (hC.next c c.2)

theorem nextTime_min (hC : IsCutSet σ C) (c : C) {k : ℕ} (hk : 0 < k)
    (hmem : (σ ^ (k : ℤ)) (c : ℕ) ∈ C) : hC.nextTime c ≤ k := by
  classical
  exact Nat.find_min' (hC.next c c.2) ⟨hk, hmem⟩

/-- The first positive backward time at which the orbit of a cut reaches another cut. -/
noncomputable def prevTime (hC : IsCutSet σ C) (c : C) : ℕ := by
  classical
  exact Nat.find (hC.prev c c.2)

theorem prevTime_spec (hC : IsCutSet σ C) (c : C) :
    0 < hC.prevTime c ∧ (σ ^ (-(hC.prevTime c : ℤ))) (c : ℕ) ∈ C := by
  classical
  exact Nat.find_spec (hC.prev c c.2)

theorem prevTime_min (hC : IsCutSet σ C) (c : C) {k : ℕ} (hk : 0 < k)
    (hmem : (σ ^ (-(k : ℤ))) (c : ℕ) ∈ C) : hC.prevTime c ≤ k := by
  classical
  exact Nat.find_min' (hC.prev c c.2) ⟨hk, hmem⟩

noncomputable def nextCut (hC : IsCutSet σ C) (c : C) : C :=
  ⟨(σ ^ (hC.nextTime c : ℤ)) (c : ℕ), (hC.nextTime_spec c).2⟩

noncomputable def prevCut (hC : IsCutSet σ C) (c : C) : C :=
  ⟨(σ ^ (-(hC.prevTime c : ℤ))) (c : ℕ), (hC.prevTime_spec c).2⟩

theorem prevCut_nextCut (hC : IsCutSet σ C) (c : C) : hC.prevCut (hC.nextCut c) = c := by
  let t := hC.nextTime c
  let d := hC.nextCut c
  let u := hC.prevTime d
  have ht := hC.nextTime_spec c
  have hu := hC.prevTime_spec d
  have hd : (d : ℕ) = (σ ^ (t : ℤ)) (c : ℕ) := rfl
  have hct : (σ ^ (-(t : ℤ))) (d : ℕ) = (c : ℕ) := by
    rw [hd, perm_zpow_apply_zpow]
    simp
  have hut : u ≤ t := hC.prevTime_min d ht.1 (hct ▸ c.property)
  have htu : t ≤ u := by
    by_contra h
    have hut' : u < t := Nat.lt_of_not_ge h
    have hcut : (σ ^ ((t - u : ℕ) : ℤ)) (c : ℕ) ∈ C := by
      convert hu.2 using 1
      rw [hd, perm_zpow_apply_zpow]
      congr 3
      omega
    have hmin : t ≤ t - u := hC.nextTime_min c (Nat.sub_pos_of_lt hut') hcut
    have := hu.1
    omega
  apply Subtype.ext
  change (σ ^ (-(u : ℤ))) (d : ℕ) = (c : ℕ)
  rw [le_antisymm hut htu]
  exact hct

theorem nextCut_prevCut (hC : IsCutSet σ C) (c : C) : hC.nextCut (hC.prevCut c) = c := by
  let t := hC.prevTime c
  let d := hC.prevCut c
  let u := hC.nextTime d
  have ht := hC.prevTime_spec c
  have hu := hC.nextTime_spec d
  have hd : (d : ℕ) = (σ ^ (-(t : ℤ))) (c : ℕ) := rfl
  have hct : (σ ^ (t : ℤ)) (d : ℕ) = (c : ℕ) := by
    rw [hd, perm_zpow_apply_zpow]
    simp
  have hut : u ≤ t := hC.nextTime_min d ht.1 (hct ▸ c.property)
  have htu : t ≤ u := by
    by_contra h
    have hut' : u < t := Nat.lt_of_not_ge h
    have hcut : (σ ^ (-((t - u : ℕ) : ℤ))) (c : ℕ) ∈ C := by
      convert hu.2 using 1
      rw [hd, perm_zpow_apply_zpow]
      congr 3
      omega
    have hmin : t ≤ t - u := hC.prevTime_min c (Nat.sub_pos_of_lt hut') hcut
    have := hu.1
    omega
  apply Subtype.ext
  change (σ ^ (u : ℤ)) (d : ℕ) = (c : ℕ)
  rw [le_antisymm hut htu]
  exact hct

/-- The original successor operation on the cuts. -/
noncomputable def cutPerm (hC : IsCutSet σ C) : Equiv.Perm C where
  toFun := hC.nextCut
  invFun := hC.prevCut
  left_inv := hC.prevCut_nextCut
  right_inv := hC.nextCut_prevCut

/-- A one-orbit permutation of the cuts. -/
noncomputable def fused (hC : IsCutSet σ C) : Equiv.Perm C := by
  letI : Infinite C := Set.infinite_coe_iff.mpr hC.infinite
  let e : C ≃ ℤ := Classical.choice nonempty_equiv_of_countable
  exact (e.trans (Equiv.addRight (1 : ℤ))).trans e.symm

theorem fused_sameCycle (hC : IsCutSet σ C) (a b : C) :
    Equiv.Perm.SameCycle hC.fused a b := by
  let _ : Infinite C := Set.infinite_coe_iff.mpr hC.infinite
  exact conjugate_intShift_sameCycle
    (Classical.choice (nonempty_equiv_of_countable : Nonempty (C ≃ ℤ))) a b

/-- Reconnect the segment successor so the induced successor on segments is `fused`. -/
noncomputable def reconnect (hC : IsCutSet σ C) : Equiv.Perm C :=
  hC.fused * hC.cutPerm⁻¹

theorem reconnect_next (hC : IsCutSet σ C) (c : C) :
    hC.reconnect (hC.nextCut c) = hC.fused c := by
  change hC.fused (hC.prevCut (hC.nextCut c)) = hC.fused c
  rw [prevCut_nextCut]

/-- The reconnection, extended by the identity off the cuts. -/
noncomputable def reconnectExt (hC : IsCutSet σ C) : Equiv.Perm ℕ := by
  classical
  exact hC.reconnect.extendDomain (Equiv.refl C)

theorem reconnectExt_apply_mem (hC : IsCutSet σ C) (c : C) :
    hC.reconnectExt (c : ℕ) = (hC.reconnect c : ℕ) := by
  classical
  change (hC.reconnect.extendDomain (Equiv.refl _)) (c : ℕ) = _
  simpa using Equiv.Perm.extendDomain_apply_image hC.reconnect (Equiv.refl C) c

theorem reconnectExt_apply_not_mem (hC : IsCutSet σ C) {n : ℕ} (hn : n ∉ C) :
    hC.reconnectExt n = n := by
  classical
  simp [reconnectExt, Equiv.Perm.extendDomain_apply_not_subtype, hn]

/-- **The glued permutation.**  Follow `σ`, then reconnect at the cuts. -/
noncomputable def glue (hC : IsCutSet σ C) : Equiv.Perm ℕ :=
  hC.reconnectExt * σ

theorem glue_apply (hC : IsCutSet σ C) (n : ℕ) : hC.glue n = hC.reconnectExt (σ n) := rfl

theorem glue_apply_of_not_mem (hC : IsCutSet σ C) {n : ℕ} (hn : σ n ∉ C) :
    hC.glue n = σ n := by
  rw [glue_apply, hC.reconnectExt_apply_not_mem hn]

theorem glue_iterate_eq (hC : IsCutSet σ C) {x k : ℕ}
    (hfree : ∀ r < k, (σ ^ (r + 1)) x ∉ C) : (hC.glue ^ k) x = (σ ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih (fun r hr => hfree r (by omega))]
      rw [hC.glue_apply_of_not_mem]
      · rw [← Equiv.Perm.mul_apply, ← pow_succ']
      · simpa only [← Equiv.Perm.mul_apply, ← pow_succ'] using hfree k (by omega)

theorem glue_to_next_segment (hC : IsCutSet σ C) (c : C) :
    (hC.glue ^ hC.nextTime c) (c : ℕ) = (hC.fused c : ℕ) := by
  let t := hC.nextTime c
  have ht := hC.nextTime_spec c
  have hfree : ∀ r < t - 1, (σ ^ (r + 1)) (c : ℕ) ∉ C := by
    intro r hr hmem
    have hmin : t ≤ r + 1 :=
      hC.nextTime_min c (by omega) (by simpa only [zpow_natCast] using hmem)
    omega
  have htrav : (hC.glue ^ (t - 1)) (c : ℕ) = (σ ^ (t - 1)) (c : ℕ) :=
    hC.glue_iterate_eq hfree
  calc
    (hC.glue ^ hC.nextTime c) (c : ℕ) = hC.glue ((hC.glue ^ (t - 1)) (c : ℕ)) := by
      rw [show hC.nextTime c = (t - 1) + 1 by dsimp only [t]; omega]
      rw [pow_succ', Equiv.Perm.mul_apply]
    _ = hC.glue ((σ ^ (t - 1)) (c : ℕ)) := by rw [htrav]
    _ = hC.reconnectExt (σ ((σ ^ (t - 1)) (c : ℕ))) := rfl
    _ = hC.reconnectExt (hC.nextCut c : ℕ) := by
      congr 1
      change σ ((σ ^ (t - 1)) (c : ℕ)) = (σ ^ (t : ℤ)) (c : ℕ)
      rw [zpow_natCast, ← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    _ = (hC.reconnect (hC.nextCut c) : ℕ) := hC.reconnectExt_apply_mem _
    _ = (hC.fused c : ℕ) := by rw [reconnect_next]

theorem glue_sameCycle_fused (hC : IsCutSet σ C) (c : C) :
    Equiv.Perm.SameCycle hC.glue (c : ℕ) (hC.fused c : ℕ) := by
  refine ⟨(hC.nextTime c : ℤ), ?_⟩
  simpa only [zpow_natCast] using hC.glue_to_next_segment c

theorem glue_sameCycle_fused_zpow (hC : IsCutSet σ C) (j : ℤ) (c : C) :
    Equiv.Perm.SameCycle hC.glue (c : ℕ) ((hC.fused ^ j) c : ℕ) := by
  induction j using Int.induction_on with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ j ih =>
      apply ih.trans
      have h := hC.glue_sameCycle_fused ((hC.fused ^ (j : ℤ)) c)
      have heq : hC.fused ((hC.fused ^ (j : ℤ)) c) = (hC.fused ^ ((j : ℤ) + 1)) c := by
        rw [← Equiv.Perm.mul_apply, ← zpow_one_add, add_comm]
      rwa [heq] at h
  | pred j ih =>
      apply ih.trans
      have h := hC.glue_sameCycle_fused ((hC.fused ^ (-(j : ℤ) - 1)) c)
      have heq : hC.fused ((hC.fused ^ (-(j : ℤ) - 1)) c) = (hC.fused ^ (-(j : ℤ))) c := by
        rw [← Equiv.Perm.mul_apply, ← zpow_one_add]
        congr 2
        omega
      rw [heq] at h
      exact h.symm

theorem glue_sameCycle_cuts (hC : IsCutSet σ C) (a b : C) :
    Equiv.Perm.SameCycle hC.glue (a : ℕ) (b : ℕ) := by
  obtain ⟨j, hj⟩ := hC.fused_sameCycle a b
  rw [← hj]
  exact hC.glue_sameCycle_fused_zpow j a

theorem glue_sameCycle_some_cut (hC : IsCutSet σ C) {x : ℕ}
    (hx : ∃ k : ℕ, (σ ^ (k : ℤ)) x ∈ C) :
    ∃ c : C, Equiv.Perm.SameCycle hC.glue x (c : ℕ) := by
  classical
  let k := Nat.find hx
  have hk : (σ ^ (k : ℤ)) x ∈ C := Nat.find_spec hx
  let c : C := ⟨(σ ^ (k : ℤ)) x, hk⟩
  by_cases hk0 : k = 0
  · refine ⟨c, ?_⟩
    have hc : (c : ℕ) = x := by simp [c, hk0]
    rw [hc]
  · refine ⟨hC.reconnect c, ⟨(k : ℤ), ?_⟩⟩
    have hfree : ∀ r < k - 1, (σ ^ (r + 1)) x ∉ C := by
      intro r hr hmem
      have hmin : k ≤ r + 1 := Nat.find_min' hx (by simpa only [zpow_natCast] using hmem)
      omega
    have htrav : (hC.glue ^ (k - 1)) x = (σ ^ (k - 1)) x := hC.glue_iterate_eq hfree
    rw [zpow_natCast, show k = (k - 1) + 1 by omega, pow_succ', Equiv.Perm.mul_apply, htrav]
    rw [glue_apply]
    have hnext : σ ((σ ^ (k - 1)) x) = (c : ℕ) := by
      change σ ((σ ^ (k - 1)) x) = (σ ^ (k : ℤ)) x
      rw [zpow_natCast, ← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    rw [hnext, reconnectExt_apply_mem]

/-- **Connectivity.**  Two points whose forward `σ`-orbits reach the cuts share a glued orbit. -/
theorem glue_connects (hC : IsCutSet σ C) {a b : ℕ}
    (ha : ∃ k : ℕ, (σ ^ (k : ℤ)) a ∈ C) (hb : ∃ k : ℕ, (σ ^ (k : ℤ)) b ∈ C) :
    ∃ j : ℤ, (hC.glue ^ j) a = b := by
  obtain ⟨ca, hca⟩ := hC.glue_sameCycle_some_cut ha
  obtain ⟨cb, hcb⟩ := hC.glue_sameCycle_some_cut hb
  exact hca.trans (hC.glue_sameCycle_cuts ca cb) |>.trans hcb.symm

end IsCutSet

end CollatzMoonshot.Amusical
