/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalReglue.GlueWith

/-!
# Segments of a cut set

The segment of a cut `c` is `c, σ c, …, σ^{t-1} c` with `t = nextTime c`.  Segments are disjoint
(`seg_eq`), cover every point with a cut in its backward orbit (`exists_seg`), and have a least
point `segMin`.  A forward survivor of a glued map lies below the minimum of every later segment
(`le_segMin_of_survivor`).
-/

namespace CollatzMoonshot.Amusical

namespace IsCutSet

variable {σ : Equiv.Perm ℕ} {C : Set ℕ}

theorem seg_eq (hC : IsCutSet σ C) {c c' : C} {r r' : ℕ} (hr : r < hC.nextTime c)
    (hr' : r' < hC.nextTime c') (h : (σ ^ r) (c : ℕ) = (σ ^ r') (c' : ℕ)) : c = c' ∧ r = r' := by
  wlog hle : r' ≤ r generalizing c c' r r'
  · obtain ⟨h1, h2⟩ := this hr' hr h.symm (by omega)
    exact ⟨h1.symm, h2.symm⟩
  have hc' : (c' : ℕ) = (σ ^ ((r - r' : ℕ) : ℤ)) (c : ℕ) := by
    have : (σ ^ (r' : ℤ)) (c' : ℕ) = (σ ^ (r' : ℤ)) ((σ ^ ((r - r' : ℕ) : ℤ)) (c : ℕ)) := by
      rw [← Equiv.Perm.mul_apply, ← zpow_add, zpow_natCast, ← h, ← zpow_natCast]
      congr 2
      omega
    exact (σ ^ (r' : ℤ)).injective this
  rcases Nat.eq_zero_or_pos (r - r') with h0 | hpos
  · refine ⟨Subtype.ext ?_, by omega⟩
    rw [hc', h0]; simp
  · have := hC.nextTime_min c hpos (hc' ▸ c'.2)
    omega

/-- Every point with a cut in its backward orbit lies in a segment. -/
theorem exists_seg (hC : IsCutSet σ C) {x : ℕ} (hx : ∃ k : ℕ, (σ ^ (-(k : ℤ))) x ∈ C) :
    ∃ c : C, ∃ r < hC.nextTime c, (σ ^ r) (c : ℕ) = x := by
  classical
  let k := Nat.find hx
  have hk : (σ ^ (-(k : ℤ))) x ∈ C := Nat.find_spec hx
  let c : C := ⟨_, hk⟩
  have hcx : (σ ^ k) (c : ℕ) = x := by
    change (σ ^ k) ((σ ^ (-(k : ℤ))) x) = x
    rw [← zpow_natCast, ← Equiv.Perm.mul_apply, ← zpow_add]; simp
  refine ⟨c, k, ?_, hcx⟩
  by_contra hlt
  push_neg at hlt
  have ht := hC.nextTime_spec c
  have hmin := Nat.find_min' hx (m := k - hC.nextTime c) (by
    have : (σ ^ (-((k - hC.nextTime c : ℕ) : ℤ))) x = (σ ^ (hC.nextTime c : ℤ)) (c : ℕ) := by
      rw [← hcx, ← zpow_natCast, ← Equiv.Perm.mul_apply, ← zpow_add]
      congr 2
      omega
    rw [this]; exact ht.2)
  have := ht.1
  omega

theorem nextTime_pos' (hC : IsCutSet σ C) (c : C) : 0 < hC.nextTime c := (hC.nextTime_spec c).1

/-- The least point of the segment of `c`. -/
noncomputable def segMin (hC : IsCutSet σ C) (c : C) : ℕ :=
  ((Finset.range (hC.nextTime c)).image fun r => (σ ^ r) (c : ℕ)).min'
    (by simpa using (hC.nextTime_pos' c).ne')

theorem segMin_mem (hC : IsCutSet σ C) (c : C) :
    ∃ r < hC.nextTime c, (σ ^ r) (c : ℕ) = hC.segMin c := by
  have := Finset.min'_mem ((Finset.range (hC.nextTime c)).image fun r => (σ ^ r) (c : ℕ))
    (by simpa using (hC.nextTime_pos' c).ne')
  simpa [segMin] using this

theorem segMin_le (hC : IsCutSet σ C) (c : C) {r : ℕ} (hr : r < hC.nextTime c) :
    hC.segMin c ≤ (σ ^ r) (c : ℕ) :=
  Finset.min'_le _ _ (Finset.mem_image.2 ⟨r, Finset.mem_range.2 hr, rfl⟩)

theorem segMin_injective (hC : IsCutSet σ C) : Function.Injective hC.segMin := by
  intro c c' h
  obtain ⟨r, hr, hrc⟩ := hC.segMin_mem c
  obtain ⟨r', hr', hrc'⟩ := hC.segMin_mem c'
  exact (hC.seg_eq hr hr' (hrc.trans (h.trans hrc'.symm))).1

theorem finite_segMin_lt (hC : IsCutSet σ C) (Z : ℕ) : {c : C | hC.segMin c < Z}.Finite := by
  refine Set.Finite.of_finite_image ((Set.finite_lt_nat Z).subset ?_)
    hC.segMin_injective.injOn
  rintro _ ⟨c, hc, rfl⟩
  exact hc

/-- The points of the segments with minimum below `Z` form a finite set. -/
theorem finite_seg_points (hC : IsCutSet σ C) (Z : ℕ) :
    {x | ∃ c : C, hC.segMin c < Z ∧ ∃ r < hC.nextTime c, (σ ^ r) (c : ℕ) = x}.Finite := by
  have : {x | ∃ c : C, hC.segMin c < Z ∧ ∃ r < hC.nextTime c, (σ ^ r) (c : ℕ) = x} =
      ⋃ c ∈ {c : C | hC.segMin c < Z},
        (fun r => (σ ^ r) (c : ℕ)) '' {r | r < hC.nextTime c} := by
    ext x; simp
  rw [this]
  exact (hC.finite_segMin_lt Z).biUnion fun c _ => (Set.finite_lt_nat _).image _

/-- A forward survivor of the glued map lies below the minimum of every later segment. -/
theorem le_segMin_of_survivor (hC : IsCutSet σ C) (φ : Equiv.Perm C) {c : C} {r : ℕ}
    (hr : r < hC.nextTime c) (hsurv : ∀ t : ℕ, (σ ^ r) (c : ℕ) ≤ (⇑(hC.glueWith φ))^[t]
      ((σ ^ r) (c : ℕ))) {k : ℕ} (hk : 1 ≤ k) :
    (σ ^ r) (c : ℕ) ≤ hC.segMin ((φ ^ k) c) := by
  set π := hC.glueWith φ
  have hpow (t : ℕ) (y : ℕ) : (⇑π)^[t] y = (π ^ t) y := by rw [Equiv.Perm.coe_pow]
  have h0 : (π ^ (hC.nextTime c - r)) ((σ ^ r) (c : ℕ)) = (φ c : ℕ) := by
    rw [← hC.glueWith_pow_of_lt φ c hr, ← Equiv.Perm.mul_apply, ← pow_add,
      Nat.sub_add_cancel hr.le, glueWith_to_next_segment]
  obtain ⟨t1, ht1⟩ := hC.glueWith_reaches φ (φ c) (k - 1)
  obtain ⟨r', hr', hrc'⟩ := hC.segMin_mem ((φ ^ k) c)
  have hφk : (φ ^ (k - 1)) (φ c) = (φ ^ k) c := by
    rw [← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hk]
  have := hsurv (r' + t1 + (hC.nextTime c - r))
  rw [hpow, pow_add, pow_add, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h0, ht1, hφk,
    hC.glueWith_pow_of_lt φ _ hr', hrc'] at this
  exact this

end IsCutSet

end CollatzMoonshot.Amusical
