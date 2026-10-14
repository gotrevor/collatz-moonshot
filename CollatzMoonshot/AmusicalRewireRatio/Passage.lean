/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalReturns
import CollatzMoonshot.AmusicalRewireRatio.Restriction

/-! Escape and first-passage infrastructure for the bounded-ratio rewiring. -/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- Uniform upper and lower affine bounds for one forward amusical step. -/
theorem amusical_step_bounds {n : ℤ} (hn : 0 ≤ n) :
    3 * n - 1 ≤ 4 * amusical n ∧ 2 * amusical n ≤ 3 * n := by
  unfold amusical
  split_ifs <;> omega

/-- Uniform upper and lower affine bounds for one backward amusical step. -/
theorem amusicalInv_step_bounds {n : ℤ} (hn : 0 ≤ n) :
    2 * n ≤ 3 * amusicalInv n ∧ 3 * amusicalInv n ≤ 4 * n + 3 := by
  unfold amusicalInv
  split_ifs <;> omega

theorem amusicalNatPerm_step_bounds (n : ℕ) :
    3 * n ≤ 4 * amusicalNatPerm n + 1 ∧ 2 * amusicalNatPerm n ≤ 3 * n := by
  have h := amusical_step_bounds (Int.natCast_nonneg n)
  rw [← amusicalNatPerm_apply_cast] at h
  constructor
  · exact_mod_cast (show 3 * (n : ℤ) ≤ 4 * (amusicalNatPerm n : ℤ) + 1 by omega)
  · exact_mod_cast h.2

theorem amusicalNatPerm_symm_step_bounds (n : ℕ) :
    2 * n ≤ 3 * amusicalNatPerm.symm n ∧
      3 * amusicalNatPerm.symm n ≤ 4 * n + 3 := by
  have h := amusicalInv_step_bounds (Int.natCast_nonneg n)
  rw [← amusicalNatPerm_symm_apply_cast] at h
  exact_mod_cast h

/-- An injective integer-indexed sequence in `ℕ` eventually leaves every bounded interval in
both directions. -/
theorem injective_eventually_abs_gt {f : ℤ → ℕ} (hinj : Function.Injective f) (B : ℕ) :
    ∃ K : ℕ, ∀ j : ℤ, K ≤ j.natAbs → B < f j := by
  have hfinite : (f ⁻¹' Set.Iic B).Finite :=
    (Set.finite_Iic B).preimage hinj.injOn
  obtain ⟨K, hK⟩ := (hfinite.image Int.natAbs).bddAbove
  refine ⟨K + 1, fun j hj ↦ ?_⟩
  by_contra hle
  have hjmem : j ∈ f ⁻¹' Set.Iic B := by
    change f j ≤ B
    omega
  have habs : j.natAbs ≤ K := hK ⟨j, hjmem, rfl⟩
  omega

/-- A natural point on an infinite amusical orbit eventually exceeds every height in both time
directions. -/
theorem amusicalNatPerm_zpow_eventually_gt_of_infinite {x : ℕ}
    (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    ∃ K : ℕ, ∀ j : ℤ, K ≤ j.natAbs → B < (amusicalNatPerm ^ j) x := by
  apply injective_eventually_abs_gt _ B
  intro i j hij
  apply amusicalPerm_zpow_apply_injective_of_infinite hinf
  have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) hij
  simpa using hcast

/-- Both a forward and a backward passage above any prescribed height exist on an infinite
nonnegative amusical orbit. -/
theorem exists_forward_backward_above {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    ∃ p q : ℕ, B < (amusicalNatPerm ^ (p : ℤ)) x ∧
      B < (amusicalNatPerm ^ (-(q : ℤ))) x := by
  obtain ⟨K, hK⟩ := amusicalNatPerm_zpow_eventually_gt_of_infinite hinf B
  refine ⟨K, K, hK K ?_, hK (-K) ?_⟩ <;> simp

theorem exists_forward_above {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    ∃ p : ℕ, B < (amusicalNatPerm ^ (p : ℤ)) x := by
  obtain ⟨p, _, hp, _⟩ := exists_forward_backward_above hinf B
  exact ⟨p, hp⟩

theorem exists_backward_above {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    ∃ q : ℕ, B < (amusicalNatPerm ^ (-(q : ℤ))) x := by
  obtain ⟨_, q, _, hq⟩ := exists_forward_backward_above hinf B
  exact ⟨q, hq⟩

/-- The first nonnegative time at which an infinite orbit passes above `B`. -/
noncomputable def forwardPassage {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) : ℕ :=
  Nat.find (exists_forward_above hinf B)

/-- The first nonpositive time at which an infinite orbit passes above `B`. -/
noncomputable def backwardPassage {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) : ℕ :=
  Nat.find (exists_backward_above hinf B)

theorem forwardPassage_gt {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    B < (amusicalNatPerm ^ (forwardPassage hinf B : ℤ)) x := by
  exact Nat.find_spec (exists_forward_above hinf B)

theorem backwardPassage_gt {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    B < (amusicalNatPerm ^ (-(backwardPassage hinf B : ℤ))) x := by
  exact Nat.find_spec (exists_backward_above hinf B)

theorem forwardPassage_before_le {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B t : ℕ)
    (ht : t < forwardPassage hinf B) :
    (amusicalNatPerm ^ (t : ℤ)) x ≤ B := by
  by_contra hgt
  have hmin : forwardPassage hinf B ≤ t :=
    Nat.find_min' (exists_forward_above hinf B) (by omega)
  omega

theorem backwardPassage_before_le {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B t : ℕ)
    (ht : t < backwardPassage hinf B) :
    (amusicalNatPerm ^ (-(t : ℤ))) x ≤ B := by
  by_contra hgt
  have hmin : backwardPassage hinf B ≤ t :=
    Nat.find_min' (exists_backward_above hinf B) (by omega)
  omega

theorem forwardPassage_pos {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ)
    (hx : x ≤ B) : 0 < forwardPassage hinf B := by
  by_contra hpos
  have hp : forwardPassage hinf B = 0 := by omega
  have hgt := forwardPassage_gt hinf B
  simp only [hp, Int.ofNat_zero, zpow_zero, Equiv.Perm.one_apply] at hgt
  omega

theorem backwardPassage_pos {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ)
    (hx : x ≤ B) : 0 < backwardPassage hinf B := by
  by_contra hpos
  have hq : backwardPassage hinf B = 0 := by omega
  have hgt := backwardPassage_gt hinf B
  simp only [hq, Int.ofNat_zero, neg_zero, zpow_zero, Equiv.Perm.one_apply] at hgt
  omega

theorem amusicalNatPerm_apply_zpow_nat_succ (x q : ℕ) :
    amusicalNatPerm ((amusicalNatPerm ^ (q : ℤ)) x) =
      (amusicalNatPerm ^ ((q + 1 : ℕ) : ℤ)) x := by
  rw [← Equiv.Perm.mul_apply]
  rw [show ((q + 1 : ℕ) : ℤ) = 1 + (q : ℤ) by omega, zpow_add, zpow_one]

theorem amusicalNatPerm_apply_zpow_neg_succ (x q : ℕ) :
    amusicalNatPerm ((amusicalNatPerm ^ (-((q + 1 : ℕ) : ℤ))) x) =
      (amusicalNatPerm ^ (-(q : ℤ))) x := by
  rw [← Equiv.Perm.mul_apply]
  rw [show -(q : ℤ) = 1 + -((q + 1 : ℕ) : ℤ) by omega, zpow_add, zpow_one]

/-- The source of the edge crossing `B` for the first time in the forward direction. -/
noncomputable def forwardCutSource {x : ℕ} (hinf : (amusicalOrbit x).Infinite)
    (B : ℕ) : ℕ :=
  (amusicalNatPerm ^ ((forwardPassage hinf B - 1 : ℕ) : ℤ)) x

/-- The target of the edge crossing `B` for the first time in the forward direction. -/
noncomputable def forwardCutTarget {x : ℕ} (hinf : (amusicalOrbit x).Infinite)
    (B : ℕ) : ℕ :=
  (amusicalNatPerm ^ (forwardPassage hinf B : ℤ)) x

/-- The source of the edge crossing `B` for the first time in the backward direction. -/
noncomputable def backwardCutSource {x : ℕ} (hinf : (amusicalOrbit x).Infinite)
    (B : ℕ) : ℕ :=
  (amusicalNatPerm ^ (-(backwardPassage hinf B : ℤ))) x

/-- The target of the edge crossing `B` for the first time in the backward direction. -/
noncomputable def backwardCutTarget {x : ℕ} (hinf : (amusicalOrbit x).Infinite)
    (B : ℕ) : ℕ :=
  (amusicalNatPerm ^ (-((backwardPassage hinf B - 1 : ℕ) : ℤ))) x

theorem forwardCutSource_le {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ)
    (hx : x ≤ B) : forwardCutSource hinf B ≤ B := by
  have hp := forwardPassage_pos hinf B hx
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  simp only [forwardCutSource, hq, Nat.succ_sub_one]
  exact forwardPassage_before_le hinf B q (by omega)

theorem forwardCutTarget_gt {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    B < forwardCutTarget hinf B :=
  forwardPassage_gt hinf B

theorem forwardCut_map {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ)
    (hx : x ≤ B) :
    amusicalNatPerm (forwardCutSource hinf B) = forwardCutTarget hinf B := by
  have hp := forwardPassage_pos hinf B hx
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  simp only [forwardCutSource, forwardCutTarget, hq, Nat.succ_sub_one]
  exact amusicalNatPerm_apply_zpow_nat_succ x q

theorem backwardCutSource_gt {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ) :
    B < backwardCutSource hinf B :=
  backwardPassage_gt hinf B

theorem backwardCutTarget_le {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ)
    (hx : x ≤ B) : backwardCutTarget hinf B ≤ B := by
  have hq := backwardPassage_pos hinf B hx
  obtain ⟨q, hq'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  simp only [backwardCutTarget, hq', Nat.succ_sub_one]
  exact backwardPassage_before_le hinf B q (by omega)

theorem backwardCut_map {x : ℕ} (hinf : (amusicalOrbit x).Infinite) (B : ℕ)
    (hx : x ≤ B) :
    amusicalNatPerm (backwardCutSource hinf B) = backwardCutTarget hinf B := by
  have hq := backwardPassage_pos hinf B hx
  obtain ⟨q, hq'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  simp only [backwardCutSource, backwardCutTarget, hq', Nat.succ_sub_one]
  exact amusicalNatPerm_apply_zpow_neg_succ x q

/-- A cut edge whose source and target lie in the uniform scale windows needed for rewiring. -/
structure AmusicalScaleCut (B : ℕ) where
  source : ℕ
  target : ℕ
  map_source : amusicalNatPerm source = target
  source_lower : 2 * B ≤ 3 * source
  source_upper : 3 * source ≤ 4 * B + 3
  target_lower : 3 * B ≤ 4 * target + 1
  target_upper : 2 * target ≤ 3 * B

/-- The forward first-passage edge, with all source and target scale bounds packaged. -/
noncomputable def forwardScaleCut {x : ℕ} (hinf : (amusicalOrbit x).Infinite)
    (B : ℕ) (hx : x ≤ B) : AmusicalScaleCut B where
  source := forwardCutSource hinf B
  target := forwardCutTarget hinf B
  map_source := forwardCut_map hinf B hx
  source_lower := by
    have hstep := (amusicalNatPerm_step_bounds (forwardCutSource hinf B)).2
    rw [forwardCut_map hinf B hx] at hstep
    have hgt := forwardCutTarget_gt hinf B
    omega
  source_upper := by
    have hle := forwardCutSource_le hinf B hx
    omega
  target_lower := by
    have hgt := forwardCutTarget_gt hinf B
    omega
  target_upper := by
    have hstep := (amusicalNatPerm_step_bounds (forwardCutSource hinf B)).2
    rw [forwardCut_map hinf B hx] at hstep
    have hle := forwardCutSource_le hinf B hx
    omega

/-- The backward first-passage edge, with all source and target scale bounds packaged. -/
noncomputable def backwardScaleCut {x : ℕ} (hinf : (amusicalOrbit x).Infinite)
    (B : ℕ) (hx : x ≤ B) : AmusicalScaleCut B where
  source := backwardCutSource hinf B
  target := backwardCutTarget hinf B
  map_source := backwardCut_map hinf B hx
  source_lower := by
    have hgt := backwardCutSource_gt hinf B
    omega
  source_upper := by
    have hstep := (amusicalNatPerm_step_bounds (backwardCutSource hinf B)).1
    rw [backwardCut_map hinf B hx] at hstep
    have hle := backwardCutTarget_le hinf B hx
    omega
  target_lower := by
    have hstep := (amusicalNatPerm_step_bounds (backwardCutSource hinf B)).1
    rw [backwardCut_map hinf B hx] at hstep
    have hgt := backwardCutSource_gt hinf B
    omega
  target_upper := by
    have hle := backwardCutTarget_le hinf B hx
    omega

namespace AmusicalScaleCut

/-- Targets of any two cut edges at one scale satisfy the target theorem's ratio bound. -/
theorem target_ratio {B : ℕ} (c d : AmusicalScaleCut B) :
    c.target ≤ 3 * d.target + 3 ∧ d.target ≤ 3 * c.target + 3 := by
  have hc := c.target_upper
  have hc' := c.target_lower
  have hd := d.target_upper
  have hd' := d.target_lower
  constructor <;> omega

/-- Sources of cut edges at scales growing by eight are strictly separated. -/
theorem source_lt_of_eight_mul_le {B C : ℕ} (c : AmusicalScaleCut B)
    (d : AmusicalScaleCut C) (hB : 0 < B) (hBC : 8 * B ≤ C) :
    c.source < d.source := by
  have hc := c.source_upper
  have hd := d.source_lower
  omega

/-- Targets of cut edges at scales growing by eight are strictly separated. -/
theorem target_lt_of_eight_mul_le {B C : ℕ} (c : AmusicalScaleCut B)
    (d : AmusicalScaleCut C) (hB : 0 < B) (hBC : 8 * B ≤ C) :
    c.target < d.target := by
  have hc := c.target_upper
  have hd := d.target_lower
  omega

end AmusicalScaleCut

end CollatzMoonshot.Amusical
