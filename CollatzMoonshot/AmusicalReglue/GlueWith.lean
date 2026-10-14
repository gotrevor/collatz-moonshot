/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalOddRewire.CutSet

/-!
# Reconnecting along a cut set in a prescribed segment order

`IsCutSet.glue` strings the segments of a cut set into one orbit in an arbitrary order.
`IsCutSet.glueWith hC φ` does the same with the segment successor `φ : Equiv.Perm C` chosen by
the caller: from the cut `c` the glued map runs through `c`'s segment and then jumps to `φ c`.
-/

namespace CollatzMoonshot.Amusical

namespace IsCutSet

variable {σ : Equiv.Perm ℕ} {C : Set ℕ}

/-- The reconnection with segment successor `φ`, extended by the identity off the cuts. -/
noncomputable def reconnectWith (hC : IsCutSet σ C) (φ : Equiv.Perm C) : Equiv.Perm ℕ := by
  classical
  exact (φ * hC.cutPerm⁻¹).extendDomain (Equiv.refl C)

theorem reconnectWith_apply_mem (hC : IsCutSet σ C) (φ : Equiv.Perm C) (c : C) :
    hC.reconnectWith φ (c : ℕ) = ((φ * hC.cutPerm⁻¹) c : ℕ) := by
  classical
  change ((φ * hC.cutPerm⁻¹).extendDomain (Equiv.refl _)) (c : ℕ) = _
  simpa using Equiv.Perm.extendDomain_apply_image (φ * hC.cutPerm⁻¹) (Equiv.refl C) c

theorem reconnectWith_apply_not_mem (hC : IsCutSet σ C) (φ : Equiv.Perm C) {n : ℕ}
    (hn : n ∉ C) : hC.reconnectWith φ n = n := by
  classical
  simp [reconnectWith, Equiv.Perm.extendDomain_apply_not_subtype, hn]

/-- **The glued permutation with segment order `φ`.** -/
noncomputable def glueWith (hC : IsCutSet σ C) (φ : Equiv.Perm C) : Equiv.Perm ℕ :=
  hC.reconnectWith φ * σ

theorem glueWith_apply (hC : IsCutSet σ C) (φ : Equiv.Perm C) (n : ℕ) :
    hC.glueWith φ n = hC.reconnectWith φ (σ n) := rfl

theorem glueWith_apply_of_not_mem (hC : IsCutSet σ C) (φ : Equiv.Perm C) {n : ℕ}
    (hn : σ n ∉ C) : hC.glueWith φ n = σ n := by
  rw [glueWith_apply, hC.reconnectWith_apply_not_mem φ hn]

theorem glueWith_symm_apply_of_not_mem (hC : IsCutSet σ C) (φ : Equiv.Perm C) {y : ℕ}
    (hy : y ∉ C) : (hC.glueWith φ).symm y = σ.symm y := by
  rw [Equiv.symm_apply_eq, glueWith_apply, Equiv.apply_symm_apply,
    hC.reconnectWith_apply_not_mem φ hy]

theorem glueWith_iterate_eq (hC : IsCutSet σ C) (φ : Equiv.Perm C) {x k : ℕ}
    (hfree : ∀ r < k, (σ ^ (r + 1)) x ∉ C) : (hC.glueWith φ ^ k) x = (σ ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih (fun r hr => hfree r (by omega))]
      rw [hC.glueWith_apply_of_not_mem]
      · rw [← Equiv.Perm.mul_apply, ← pow_succ']
      · simpa only [← Equiv.Perm.mul_apply, ← pow_succ'] using hfree k (by omega)

/-- Inside the segment of a cut `c` the glued map is `σ`. -/
theorem glueWith_pow_of_lt (hC : IsCutSet σ C) (φ : Equiv.Perm C) (c : C) {r : ℕ}
    (hr : r < hC.nextTime c) : (hC.glueWith φ ^ r) (c : ℕ) = (σ ^ r) (c : ℕ) := by
  refine hC.glueWith_iterate_eq φ fun r' hr' hmem => ?_
  have hmin : hC.nextTime c ≤ r' + 1 :=
    hC.nextTime_min c (by omega) (by simpa only [zpow_natCast] using hmem)
  omega

theorem glueWith_to_next_segment (hC : IsCutSet σ C) (φ : Equiv.Perm C) (c : C) :
    (hC.glueWith φ ^ hC.nextTime c) (c : ℕ) = (φ c : ℕ) := by
  let t := hC.nextTime c
  have ht := hC.nextTime_spec c
  have htrav : (hC.glueWith φ ^ (t - 1)) (c : ℕ) = (σ ^ (t - 1)) (c : ℕ) :=
    hC.glueWith_pow_of_lt φ c (by omega)
  calc
    (hC.glueWith φ ^ hC.nextTime c) (c : ℕ) = hC.glueWith φ ((hC.glueWith φ ^ (t - 1)) c) := by
      rw [show hC.nextTime c = (t - 1) + 1 by dsimp only [t]; omega]
      rw [pow_succ', Equiv.Perm.mul_apply]
    _ = hC.glueWith φ ((σ ^ (t - 1)) (c : ℕ)) := by rw [htrav]
    _ = hC.reconnectWith φ (σ ((σ ^ (t - 1)) (c : ℕ))) := rfl
    _ = hC.reconnectWith φ (hC.nextCut c : ℕ) := by
      congr 1
      change σ ((σ ^ (t - 1)) (c : ℕ)) = (σ ^ (t : ℤ)) (c : ℕ)
      rw [zpow_natCast, ← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    _ = ((φ * hC.cutPerm⁻¹) (hC.nextCut c) : ℕ) := hC.reconnectWith_apply_mem φ _
    _ = (φ c : ℕ) := by
      change (φ (hC.prevCut (hC.nextCut c)) : ℕ) = _
      rw [prevCut_nextCut]

/-- From a cut, the glued map reaches every later cut of the order `φ`. -/
theorem glueWith_reaches (hC : IsCutSet σ C) (φ : Equiv.Perm C) (c : C) (k : ℕ) :
    ∃ t : ℕ, (hC.glueWith φ ^ t) (c : ℕ) = ((φ ^ k) c : ℕ) := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨hC.nextTime ((φ ^ k) c) + t, ?_⟩
      rw [pow_add, Equiv.Perm.mul_apply, ht, glueWith_to_next_segment, pow_succ',
        Equiv.Perm.mul_apply]

theorem glueWith_sameCycle_cuts (hC : IsCutSet σ C) (φ : Equiv.Perm C)
    (hφ : ∀ a b : C, φ.SameCycle a b) (a b : C) :
    Equiv.Perm.SameCycle (hC.glueWith φ) (a : ℕ) (b : ℕ) := by
  obtain ⟨j, hj⟩ := hφ a b
  rcases Int.eq_nat_or_neg j with ⟨k, rfl | rfl⟩
  · obtain ⟨t, ht⟩ := hC.glueWith_reaches φ a k
    exact ⟨t, by rw [zpow_natCast, ht, ← hj, zpow_natCast]⟩
  · have hba : (φ ^ k) b = a := by
      rw [← hj, ← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add]; simp
    obtain ⟨t, ht⟩ := hC.glueWith_reaches φ b k
    have h : Equiv.Perm.SameCycle (hC.glueWith φ) (b : ℕ) (a : ℕ) :=
      ⟨t, by rw [zpow_natCast, ht, hba]⟩
    exact h.symm

theorem glueWith_sameCycle_some_cut (hC : IsCutSet σ C) (φ : Equiv.Perm C) {x : ℕ}
    (hx : ∃ k : ℕ, (σ ^ (k : ℤ)) x ∈ C) :
    ∃ c : C, Equiv.Perm.SameCycle (hC.glueWith φ) x (c : ℕ) := by
  classical
  let k := Nat.find hx
  have hk : (σ ^ (k : ℤ)) x ∈ C := Nat.find_spec hx
  let c : C := ⟨(σ ^ (k : ℤ)) x, hk⟩
  by_cases hk0 : k = 0
  · refine ⟨c, ?_⟩
    have hc : (c : ℕ) = x := by simp [c, hk0]
    rw [hc]
  · refine ⟨(φ * hC.cutPerm⁻¹) c, ⟨(k : ℤ), ?_⟩⟩
    have hfree : ∀ r < k - 1, (σ ^ (r + 1)) x ∉ C := by
      intro r hr hmem
      have hmin : k ≤ r + 1 := Nat.find_min' hx (by simpa only [zpow_natCast] using hmem)
      omega
    have htrav : (hC.glueWith φ ^ (k - 1)) x = (σ ^ (k - 1)) x := hC.glueWith_iterate_eq φ hfree
    rw [zpow_natCast, show k = (k - 1) + 1 by omega, pow_succ', Equiv.Perm.mul_apply, htrav]
    rw [glueWith_apply]
    have hnext : σ ((σ ^ (k - 1)) x) = (c : ℕ) := by
      change σ ((σ ^ (k - 1)) x) = (σ ^ (k : ℤ)) x
      rw [zpow_natCast, ← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    rw [hnext, reconnectWith_apply_mem]

/-- **Connectivity.**  With a one-cycle segment order, two points whose forward `σ`-orbits reach
the cuts share a glued orbit. -/
theorem glueWith_sameCycle (hC : IsCutSet σ C) (φ : Equiv.Perm C)
    (hφ : ∀ a b : C, φ.SameCycle a b) {a b : ℕ}
    (ha : ∃ k : ℕ, (σ ^ (k : ℤ)) a ∈ C) (hb : ∃ k : ℕ, (σ ^ (k : ℤ)) b ∈ C) :
    Equiv.Perm.SameCycle (hC.glueWith φ) a b := by
  obtain ⟨ca, hca⟩ := hC.glueWith_sameCycle_some_cut φ ha
  obtain ⟨cb, hcb⟩ := hC.glueWith_sameCycle_some_cut φ hb
  exact hca.trans (hC.glueWith_sameCycle_cuts φ hφ ca cb) |>.trans hcb.symm

end IsCutSet

end CollatzMoonshot.Amusical
