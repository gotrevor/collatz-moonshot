/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical

/-!
# Infrastructure for sparsely rewiring infinite permutation orbits

The lemmas here isolate the properness and annulus-crossing facts used by the construction in
`rewire_single_orbit`.
-/

namespace CollatzMoonshot.Amusical

/-- The integer parametrization of an infinite orbit of a permutation has no repetitions. -/
theorem perm_zpow_apply_injective_of_infinite {α : Type*} (σ : Equiv.Perm α) {x : α}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) :
    Function.Injective fun j : ℤ => (σ ^ j) x := by
  by_contra h
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, heq, hij⟩ := h
  have hfix : (σ ^ (i - j)) x = x := by
    apply (σ ^ j).injective
    rw [← Equiv.Perm.mul_apply, ← zpow_add, show j + (i - j) = i by omega]
    simpa using heq
  let p := (i - j).natAbs
  have hp : 0 < p := Int.natAbs_pos.mpr (sub_ne_zero.mpr hij)
  have hperiod : (σ ^ (p : ℤ)) x = x := by
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hij).symm with hpos | hneg
    · simpa only [p, Int.natCast_natAbs, abs_of_pos hpos] using hfix
    · have hfixneg : (σ ^ (-(i - j))) x = x := by
        apply (σ ^ (i - j)).injective
        rw [← Equiv.Perm.mul_apply, ← zpow_add]
        simp [hfix]
      simpa only [p, Int.natCast_natAbs, abs_of_neg hneg] using hfixneg
  have hper : Function.IsPeriodicPt (fun y => σ • y) p x := by
    change (⇑σ)^[p] x = x
    rw [← Equiv.Perm.coe_pow]
    exact hperiod
  have hmin : 0 < Function.minimalPeriod (fun y => σ • y) x :=
    hper.minimalPeriod_pos hp
  letI : NeZero (Function.minimalPeriod (fun y => σ • y) x) := ⟨hmin.ne'⟩
  have horbit : (MulAction.orbit (Subgroup.zpowers σ) x).Finite := by
    rw [← Set.finite_coe_iff]
    exact (MulAction.orbitZPowersEquiv σ x).finite_iff.mpr inferInstance
  apply hinf
  convert horbit using 1
  ext y
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨σ ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨k, rfl⟩

/-- An infinite permutation orbit visits a bounded set at only finitely many integer times. -/
theorem finite_orbit_times_le {σ : Equiv.Perm ℕ} {x B : ℕ}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) :
    {j : ℤ | (σ ^ j) x ≤ B}.Finite := by
  have hinj := perm_zpow_apply_injective_of_infinite σ hinf
  exact (Set.finite_le_nat B).preimage hinj.injOn

/-- Both forward and backward halves of an infinite permutation orbit are unbounded. -/
theorem exists_nat_iterate_gt {σ : Equiv.Perm ℕ} {x : ℕ}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) (B : ℕ) :
    (∃ k : ℕ, B < (σ ^ (k : ℤ)) x) ∧ (∃ k : ℕ, B < (σ ^ (-(k : ℤ))) x) := by
  have hinj := perm_zpow_apply_injective_of_infinite σ hinf
  constructor
  · by_contra h
    push Not at h
    have hrange : (Set.range fun k : ℕ => (σ ^ (k : ℤ)) x).Finite :=
      (Set.finite_le_nat B).subset (Set.range_subset_iff.mpr h)
    exact Set.infinite_range_of_injective
      (hinj.comp Int.ofNat_injective) hrange
  · by_contra h
    push Not at h
    have hrange : (Set.range fun k : ℕ => (σ ^ (-(k : ℤ))) x).Finite :=
      (Set.finite_le_nat B).subset (Set.range_subset_iff.mpr h)
    apply Set.infinite_range_of_injective _ hrange
    exact hinj.comp fun a b hab => by simpa using congrArg Int.natAbs hab

/-- Moving the base point along a permutation orbit does not change the two-sided orbit. -/
theorem perm_zpow_range_apply_zpow (σ : Equiv.Perm ℕ) (x : ℕ) (ε : ℤ) :
    Set.range (fun j : ℤ => (σ ^ j) ((σ ^ ε) x)) =
      Set.range fun j : ℤ => (σ ^ j) x := by
  ext y
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨j + ε, ?_⟩
    change (σ ^ (j + ε)) x = (σ ^ j) ((σ ^ ε) x)
    rw [zpow_add, Equiv.Perm.mul_apply]
  · rintro ⟨j, rfl⟩
    refine ⟨j - ε, ?_⟩
    change (σ ^ (j - ε)) ((σ ^ ε) x) = (σ ^ j) x
    rw [← Equiv.Perm.mul_apply, ← zpow_add]
    congr 2
    omega

theorem perm_zpow_apply_zpow (σ : Equiv.Perm ℕ) (x : ℕ) (i j : ℤ) :
    (σ ^ i) ((σ ^ j) x) = (σ ^ (i + j)) x := by
  rw [← Equiv.Perm.mul_apply, ← zpow_add]

/-- Each tail of either half of an infinite permutation orbit is unbounded. -/
theorem exists_nat_iterate_gt_after {σ : Equiv.Perm ℕ} {x : ℕ}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) (B K : ℕ) :
    (∃ k ≥ K, B < (σ ^ (k : ℤ)) x) ∧
      ∃ k ≥ K, B < (σ ^ (-(k : ℤ))) x := by
  have shifted (ε : ℤ) :
      (Set.range fun j : ℤ => (σ ^ j) ((σ ^ ε) x)).Infinite := by
    rwa [perm_zpow_range_apply_zpow]
  constructor
  · obtain ⟨k, hk⟩ := (exists_nat_iterate_gt (shifted (K : ℤ)) B).1
    refine ⟨K + k, by omega, ?_⟩
    calc
      B < (σ ^ (k : ℤ)) ((σ ^ (K : ℤ)) x) := hk
      _ = (σ ^ ((K + k : ℕ) : ℤ)) x := by
        rw [Int.natCast_add, add_comm, zpow_add, Equiv.Perm.mul_apply]
  · obtain ⟨k, hk⟩ := (exists_nat_iterate_gt (shifted (-(K : ℤ))) B).2
    refine ⟨K + k, by omega, ?_⟩
    calc
      B < (σ ^ (-(k : ℤ))) ((σ ^ (-(K : ℤ))) x) := hk
      _ = (σ ^ (-((K + k : ℕ) : ℤ))) x := by
        rw [← Equiv.Perm.mul_apply, ← zpow_add]
        congr 2
        push_cast
        omega

/-- A chosen forward cut after time `K`, lying above the prescribed value bound `B`. -/
noncomputable def forwardSparseCutTime (σ : Equiv.Perm ℕ) (x : ℕ)
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) (B K : ℕ) : ℕ :=
  Nat.find (exists_nat_iterate_gt_after hinf B K).1

theorem forwardSparseCutTime_ge (σ : Equiv.Perm ℕ) (x : ℕ)
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) (B K : ℕ) :
    K ≤ forwardSparseCutTime σ x hinf B K :=
  (Nat.find_spec (exists_nat_iterate_gt_after hinf B K).1).1

theorem forwardSparseCutTime_gt (σ : Equiv.Perm ℕ) (x : ℕ)
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) (B K : ℕ) :
    B < (σ ^ (forwardSparseCutTime σ x hinf B K : ℤ)) x :=
  (Nat.find_spec (exists_nat_iterate_gt_after hinf B K).1).2

/-- A chosen backward cut after backward time `K`, above the prescribed value bound `B`. -/
noncomputable def backwardSparseCutTime (σ : Equiv.Perm ℕ) (x : ℕ)
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) (B K : ℕ) : ℕ :=
  Nat.find (exists_nat_iterate_gt_after hinf B K).2

theorem backwardSparseCutTime_ge (σ : Equiv.Perm ℕ) (x : ℕ)
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) (B K : ℕ) :
    K ≤ backwardSparseCutTime σ x hinf B K :=
  (Nat.find_spec (exists_nat_iterate_gt_after hinf B K).2).1

theorem backwardSparseCutTime_gt (σ : Equiv.Perm ℕ) (x : ℕ)
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) (B K : ℕ) :
    B < (σ ^ (-(backwardSparseCutTime σ x hinf B K : ℤ))) x :=
  (Nat.find_spec (exists_nat_iterate_gt_after hinf B K).2).2

/-- Decode the orbit point from the index used for the global sparse cut enumeration. -/
def sparseCutSource (q : ℕ) : ℕ := (Nat.unpair (Nat.unpair q).1).1

/-- Decode the requested minimum time from a global sparse cut index. -/
def sparseCutAfter (q : ℕ) : ℕ := (Nat.unpair (Nat.unpair q).1).2

/-- Decode the direction (`0` forward, `1` backward) from a global sparse cut index. -/
def sparseCutSide (q : ℕ) : ℕ := (Nat.unpair q).2

/-- The cut selected by index `q`.  Valid forward and backward requests use an infinite orbit;
all other indices are harmless padding.  Every value is at least `(q + 1)²`. -/
noncomputable def sparseCutPoint (σ : Equiv.Perm ℕ) (q : ℕ) : ℕ :=
  by
    classical
    exact
      if hinf : (Set.range fun j : ℤ => (σ ^ j) (sparseCutSource q)).Infinite then
        if sparseCutSide q = 0 then
          (σ ^ (forwardSparseCutTime σ (sparseCutSource q) hinf ((q + 1) ^ 2)
            (sparseCutAfter q) : ℤ)) (sparseCutSource q)
        else if sparseCutSide q = 1 then
          (σ ^ (-(backwardSparseCutTime σ (sparseCutSource q) hinf ((q + 1) ^ 2)
            (sparseCutAfter q) : ℤ))) (sparseCutSource q)
        else
          (q + 1) ^ 2
      else
        (q + 1) ^ 2

theorem sparseCutPoint_ge_square (σ : Equiv.Perm ℕ) (q : ℕ) :
    (q + 1) ^ 2 ≤ sparseCutPoint σ q := by
  unfold sparseCutPoint
  split_ifs with hinf hzero hone
  · exact (forwardSparseCutTime_gt σ _ hinf _ _).le
  · exact (backwardSparseCutTime_gt σ _ hinf _ _).le
  · exact le_rfl
  · exact le_rfl

theorem sparseCutPoint_forward (σ : Equiv.Perm ℕ) (x K : ℕ)
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) :
    sparseCutPoint σ (Nat.pair (Nat.pair x K) 0) =
      (σ ^ (forwardSparseCutTime σ x hinf
        ((Nat.pair (Nat.pair x K) 0 + 1) ^ 2) K : ℤ)) x := by
  simp [sparseCutPoint, sparseCutSource, sparseCutAfter, sparseCutSide, hinf]

theorem sparseCutPoint_backward (σ : Equiv.Perm ℕ) (x K : ℕ)
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) :
    sparseCutPoint σ (Nat.pair (Nat.pair x K) 1) =
      (σ ^ (-(backwardSparseCutTime σ x hinf
        ((Nat.pair (Nat.pair x K) 1 + 1) ^ 2) K : ℤ))) x := by
  simp [sparseCutPoint, sparseCutSource, sparseCutAfter, sparseCutSide, hinf]

/-- The valid indices in the global enumeration are the two directions based at infinite-orbit
points. -/
def IsSparseCutIndex (σ : Equiv.Perm ℕ) (q : ℕ) : Prop :=
  (sparseCutSide q = 0 ∨ sparseCutSide q = 1) ∧
    (Set.range fun j : ℤ => (σ ^ j) (sparseCutSource q)).Infinite

/-- A quadratically sparse set which meets both tails of every infinite orbit cofinally. -/
noncomputable def sparseOrbitCuts (σ : Equiv.Perm ℕ) : Set ℕ :=
  sparseCutPoint σ '' {q | IsSparseCutIndex σ q}

theorem sparseOrbitCuts_cofinal (σ : Equiv.Perm ℕ) {x : ℕ}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) :
    (∀ K : ℕ, ∃ k : ℕ, k ≥ K ∧ (σ ^ (k : ℤ)) x ∈ sparseOrbitCuts σ) ∧
      ∀ K : ℕ, ∃ k : ℕ, k ≥ K ∧ (σ ^ (-(k : ℤ))) x ∈ sparseOrbitCuts σ := by
  constructor
  · intro K
    let q := Nat.pair (Nat.pair x K) 0
    let k := forwardSparseCutTime σ x hinf ((q + 1) ^ 2) K
    refine ⟨k, forwardSparseCutTime_ge σ x hinf _ _, ?_⟩
    refine ⟨q, ?_, ?_⟩
    · simp [IsSparseCutIndex, sparseCutSource, sparseCutSide, q, hinf]
    · simpa only [q, k] using sparseCutPoint_forward σ x K hinf
  · intro K
    let q := Nat.pair (Nat.pair x K) 1
    let k := backwardSparseCutTime σ x hinf ((q + 1) ^ 2) K
    refine ⟨k, backwardSparseCutTime_ge σ x hinf _ _, ?_⟩
    refine ⟨q, ?_, ?_⟩
    · simp [IsSparseCutIndex, sparseCutSource, sparseCutSide, q, hinf]
    · simpa only [q, k] using sparseCutPoint_backward σ x K hinf

/-- Every selected cut lies on an infinite orbit. -/
theorem sparseOrbitCuts_only_infinite (σ : Equiv.Perm ℕ) {y : ℕ}
    (hy : y ∈ sparseOrbitCuts σ) :
    (Set.range fun j : ℤ => (σ ^ j) y).Infinite := by
  obtain ⟨q, ⟨hside, hinf⟩, rfl⟩ := hy
  rcases hside with hzero | hone
  · rw [show sparseCutPoint σ q =
        (σ ^ (forwardSparseCutTime σ (sparseCutSource q) hinf ((q + 1) ^ 2)
          (sparseCutAfter q) : ℤ)) (sparseCutSource q) by
      simp [sparseCutPoint, hinf, hzero]]
    rwa [perm_zpow_range_apply_zpow]
  · rw [show sparseCutPoint σ q =
        (σ ^ (-(backwardSparseCutTime σ (sparseCutSource q) hinf ((q + 1) ^ 2)
          (sparseCutAfter q) : ℤ))) (sparseCutSource q) by
      simp [sparseCutPoint, hinf, hone]]
    rwa [perm_zpow_range_apply_zpow]

theorem sparseOrbitCuts_exists_next (σ : Equiv.Perm ℕ) (c : sparseOrbitCuts σ) :
    ∃ k : ℕ, 0 < k ∧ (σ ^ (k : ℤ)) (c : ℕ) ∈ sparseOrbitCuts σ := by
  obtain ⟨k, hk, hmem⟩ :=
    (sparseOrbitCuts_cofinal σ (sparseOrbitCuts_only_infinite σ c.property)).1 1
  exact ⟨k, by omega, hmem⟩

theorem sparseOrbitCuts_exists_prev (σ : Equiv.Perm ℕ) (c : sparseOrbitCuts σ) :
    ∃ k : ℕ, 0 < k ∧ (σ ^ (-(k : ℤ))) (c : ℕ) ∈ sparseOrbitCuts σ := by
  obtain ⟨k, hk, hmem⟩ :=
    (sparseOrbitCuts_cofinal σ (sparseOrbitCuts_only_infinite σ c.property)).2 1
  exact ⟨k, by omega, hmem⟩

/-- The first positive time at which the orbit of a cut reaches another cut. -/
noncomputable def nextSparseCutTime (σ : Equiv.Perm ℕ) (c : sparseOrbitCuts σ) : ℕ :=
  by
    classical
    exact Nat.find (sparseOrbitCuts_exists_next σ c)

theorem nextSparseCutTime_spec (σ : Equiv.Perm ℕ) (c : sparseOrbitCuts σ) :
    0 < nextSparseCutTime σ c ∧
      (σ ^ (nextSparseCutTime σ c : ℤ)) (c : ℕ) ∈ sparseOrbitCuts σ :=
  by
    classical
    exact Nat.find_spec (sparseOrbitCuts_exists_next σ c)

/-- The first positive backward time at which the orbit of a cut reaches another cut. -/
noncomputable def prevSparseCutTime (σ : Equiv.Perm ℕ) (c : sparseOrbitCuts σ) : ℕ :=
  by
    classical
    exact Nat.find (sparseOrbitCuts_exists_prev σ c)

theorem prevSparseCutTime_spec (σ : Equiv.Perm ℕ) (c : sparseOrbitCuts σ) :
    0 < prevSparseCutTime σ c ∧
      (σ ^ (-(prevSparseCutTime σ c : ℤ))) (c : ℕ) ∈ sparseOrbitCuts σ :=
  by
    classical
    exact Nat.find_spec (sparseOrbitCuts_exists_prev σ c)

noncomputable def nextSparseCut (σ : Equiv.Perm ℕ) (c : sparseOrbitCuts σ) :
    sparseOrbitCuts σ :=
  ⟨(σ ^ (nextSparseCutTime σ c : ℤ)) (c : ℕ), (nextSparseCutTime_spec σ c).2⟩

noncomputable def prevSparseCut (σ : Equiv.Perm ℕ) (c : sparseOrbitCuts σ) :
    sparseOrbitCuts σ :=
  ⟨(σ ^ (-(prevSparseCutTime σ c : ℤ))) (c : ℕ), (prevSparseCutTime_spec σ c).2⟩

theorem prevSparseCut_nextSparseCut (σ : Equiv.Perm ℕ) (c : sparseOrbitCuts σ) :
    prevSparseCut σ (nextSparseCut σ c) = c := by
  classical
  let t := nextSparseCutTime σ c
  let d := nextSparseCut σ c
  let u := prevSparseCutTime σ d
  have ht := nextSparseCutTime_spec σ c
  have hu := prevSparseCutTime_spec σ d
  have hd : (d : ℕ) = (σ ^ (t : ℤ)) (c : ℕ) := rfl
  have hct : (σ ^ (-(t : ℤ))) (d : ℕ) = (c : ℕ) := by
    rw [hd, perm_zpow_apply_zpow]
    simp
  have hut : u ≤ t := by
    apply Nat.find_min' (sparseOrbitCuts_exists_prev σ d)
    exact ⟨ht.1, hct ▸ c.property⟩
  have htu : t ≤ u := by
    by_contra h
    have hut' : u < t := Nat.lt_of_not_ge h
    have hcut : (σ ^ ((t - u : ℕ) : ℤ)) (c : ℕ) ∈ sparseOrbitCuts σ := by
      convert hu.2 using 1
      rw [hd, perm_zpow_apply_zpow]
      congr 3
      push_cast
      omega
    have hmin : t ≤ t - u := by
      apply Nat.find_min' (sparseOrbitCuts_exists_next σ c)
      exact ⟨Nat.sub_pos_of_lt hut', hcut⟩
    have := hu.1
    omega
  apply Subtype.ext
  change (σ ^ (-(u : ℤ))) (d : ℕ) = (c : ℕ)
  rw [le_antisymm hut htu]
  exact hct

theorem nextSparseCut_prevSparseCut (σ : Equiv.Perm ℕ) (c : sparseOrbitCuts σ) :
    nextSparseCut σ (prevSparseCut σ c) = c := by
  classical
  let t := prevSparseCutTime σ c
  let d := prevSparseCut σ c
  let u := nextSparseCutTime σ d
  have ht := prevSparseCutTime_spec σ c
  have hu := nextSparseCutTime_spec σ d
  have hd : (d : ℕ) = (σ ^ (-(t : ℤ))) (c : ℕ) := rfl
  have hct : (σ ^ (t : ℤ)) (d : ℕ) = (c : ℕ) := by
    rw [hd, perm_zpow_apply_zpow]
    simp
  have hut : u ≤ t := by
    apply Nat.find_min' (sparseOrbitCuts_exists_next σ d)
    exact ⟨ht.1, hct ▸ c.property⟩
  have htu : t ≤ u := by
    by_contra h
    have hut' : u < t := Nat.lt_of_not_ge h
    have hcut : (σ ^ (-((t - u : ℕ) : ℤ))) (c : ℕ) ∈ sparseOrbitCuts σ := by
      convert hu.2 using 1
      rw [hd, perm_zpow_apply_zpow]
      congr 3
      push_cast
      omega
    have hmin : t ≤ t - u := by
      apply Nat.find_min' (sparseOrbitCuts_exists_prev σ c)
      exact ⟨Nat.sub_pos_of_lt hut', hcut⟩
    have := hu.1
    omega
  apply Subtype.ext
  change (σ ^ (u : ℤ)) (d : ℕ) = (c : ℕ)
  rw [le_antisymm hut htu]
  exact hct

/-- The original successor operation on the sparse cuts. -/
noncomputable def sparseCutPerm (σ : Equiv.Perm ℕ) : Equiv.Perm (sparseOrbitCuts σ) where
  toFun := nextSparseCut σ
  invFun := prevSparseCut σ
  left_inv := prevSparseCut_nextSparseCut σ
  right_inv := nextSparseCut_prevSparseCut σ

theorem sparseOrbitCuts_infinite_of_infinite_orbit (σ : Equiv.Perm ℕ) {x : ℕ}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) :
    (sparseOrbitCuts σ).Infinite := by
  let times : Set ℕ := {k | (σ ^ (k : ℤ)) x ∈ sparseOrbitCuts σ}
  have htimes : times.Infinite := Set.infinite_of_forall_exists_gt fun K => by
    obtain ⟨k, hk, hmem⟩ := (sparseOrbitCuts_cofinal σ hinf).1 (K + 1)
    exact ⟨k, hmem, by omega⟩
  have hinj : Function.Injective fun k : ℕ => (σ ^ (k : ℤ)) x :=
    (perm_zpow_apply_injective_of_infinite σ hinf).comp Int.ofNat_injective
  apply Set.Infinite.mono _ (htimes.image hinj.injOn)
  rintro y ⟨k, hk, rfl⟩
  exact hk

/-- Conjugating translation by one on `ℤ` produces a permutation with one orbit. -/
theorem conjugate_intShift_sameCycle {α : Type*} (e : α ≃ ℤ) (a b : α) :
    Equiv.Perm.SameCycle ((e.trans (Equiv.addRight (1 : ℤ))).trans e.symm) a b := by
  let p : Equiv.Perm α := (e.trans (Equiv.addRight (1 : ℤ))).trans e.symm
  have hp (j : ℤ) : ∀ x : α, (p ^ j) x = e.symm (e x + j) := by
    induction j using Int.induction_on with
    | zero => intro x; simp
    | succ j ih =>
        intro x
        rw [zpow_add_one, Equiv.Perm.mul_apply, ih]
        simp [p, Equiv.coe_addRight]
        omega
    | pred j ih =>
        intro x
        rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
        simp [p, Equiv.coe_addRight]
        omega
  refine ⟨e b - e a, ?_⟩
  rw [hp]
  rw [show e a + (e b - e a) = e b by omega, e.symm_apply_apply]

/-- A canonical one-orbit permutation of the sparse cut set, once that set is infinite. -/
noncomputable def fusedSparseCutPerm (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) : Equiv.Perm (sparseOrbitCuts σ) := by
  letI : Infinite (sparseOrbitCuts σ) := Set.infinite_coe_iff.mpr hinf
  let e : sparseOrbitCuts σ ≃ ℤ := Classical.choice nonempty_equiv_of_countable
  exact (e.trans (Equiv.addRight (1 : ℤ))).trans e.symm

theorem fusedSparseCutPerm_sameCycle (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) (a b : sparseOrbitCuts σ) :
    Equiv.Perm.SameCycle (fusedSparseCutPerm σ hinf) a b := by
  letI : Infinite (sparseOrbitCuts σ) := Set.infinite_coe_iff.mpr hinf
  exact conjugate_intShift_sameCycle
    (Classical.choice (nonempty_equiv_of_countable : Nonempty (sparseOrbitCuts σ ≃ ℤ))) a b

/-- Reconnect the original segment successor so that the induced successor on segments is the
chosen one-orbit permutation of cuts. -/
noncomputable def reconnectSparseCuts (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) : Equiv.Perm (sparseOrbitCuts σ) :=
  fusedSparseCutPerm σ hinf * (sparseCutPerm σ)⁻¹

theorem reconnectSparseCuts_next (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) (c : sparseOrbitCuts σ) :
    reconnectSparseCuts σ hinf (nextSparseCut σ c) = fusedSparseCutPerm σ hinf c := by
  change fusedSparseCutPerm σ hinf
      (prevSparseCut σ (nextSparseCut σ c)) = fusedSparseCutPerm σ hinf c
  rw [prevSparseCut_nextSparseCut]

/-- Extend the reconnection of cut points by the identity on their complement. -/
noncomputable def reconnectSparseCutsExt (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) : Equiv.Perm ℕ := by
  classical
  letI : DecidablePred (· ∈ sparseOrbitCuts σ) := Classical.decPred _
  exact (reconnectSparseCuts σ hinf).extendDomain (Equiv.refl (sparseOrbitCuts σ))

theorem reconnectSparseCutsExt_apply_mem (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) (c : sparseOrbitCuts σ) :
    reconnectSparseCutsExt σ hinf (c : ℕ) = (reconnectSparseCuts σ hinf c : ℕ) := by
  classical
  change ((reconnectSparseCuts σ hinf).extendDomain (Equiv.refl _)) (c : ℕ) = _
  simpa using Equiv.Perm.extendDomain_apply_image (reconnectSparseCuts σ hinf)
    (Equiv.refl (sparseOrbitCuts σ)) c

theorem reconnectSparseCutsExt_apply_not_mem (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) {n : ℕ} (hn : n ∉ sparseOrbitCuts σ) :
    reconnectSparseCutsExt σ hinf n = n := by
  classical
  simp [reconnectSparseCutsExt, Equiv.Perm.extendDomain_apply_not_subtype, hn]

/-- The permutation obtained by reconnecting the sparse orbit segments. -/
noncomputable def sparselyRewiredPerm (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) : Equiv.Perm ℕ :=
  reconnectSparseCutsExt σ hinf * σ

theorem sparselyRewiredPerm_apply (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) (n : ℕ) :
    sparselyRewiredPerm σ hinf n = reconnectSparseCutsExt σ hinf (σ n) := by
  rfl

theorem sparselyRewiredPerm_apply_of_not_mem (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) {n : ℕ} (hn : σ n ∉ sparseOrbitCuts σ) :
    sparselyRewiredPerm σ hinf n = σ n := by
  rw [sparselyRewiredPerm_apply, reconnectSparseCutsExt_apply_not_mem σ hinf hn]

theorem sparselyRewiredPerm_iterate_eq (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) {x k : ℕ}
    (hfree : ∀ r < k, (σ ^ (r + 1)) x ∉ sparseOrbitCuts σ) :
    (sparselyRewiredPerm σ hinf ^ k) x = (σ ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih (fun r hr => hfree r (by omega))]
      rw [sparselyRewiredPerm_apply_of_not_mem]
      · rw [← Equiv.Perm.mul_apply, ← pow_succ']
      · simpa only [← Equiv.Perm.mul_apply, ← pow_succ'] using hfree k (by omega)

theorem sparselyRewiredPerm_to_next_segment (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) (c : sparseOrbitCuts σ) :
    (sparselyRewiredPerm σ hinf ^ nextSparseCutTime σ c) (c : ℕ) =
      (fusedSparseCutPerm σ hinf c : ℕ) := by
  classical
  let t := nextSparseCutTime σ c
  have ht := nextSparseCutTime_spec σ c
  have hfree : ∀ r < t - 1, (σ ^ (r + 1)) (c : ℕ) ∉ sparseOrbitCuts σ := by
    intro r hr hmem
    have hmin : t ≤ r + 1 := by
      apply Nat.find_min' (sparseOrbitCuts_exists_next σ c)
      exact ⟨by omega, by simpa only [zpow_natCast] using hmem⟩
    omega
  have htrav :
      (sparselyRewiredPerm σ hinf ^ (t - 1)) (c : ℕ) = (σ ^ (t - 1)) (c : ℕ) :=
    sparselyRewiredPerm_iterate_eq σ hinf hfree
  calc
    (sparselyRewiredPerm σ hinf ^ nextSparseCutTime σ c) (c : ℕ) =
        sparselyRewiredPerm σ hinf
          ((sparselyRewiredPerm σ hinf ^ (t - 1)) (c : ℕ)) := by
      rw [show nextSparseCutTime σ c = (t - 1) + 1 by dsimp only [t]; omega]
      rw [pow_succ', Equiv.Perm.mul_apply]
    _ = sparselyRewiredPerm σ hinf ((σ ^ (t - 1)) (c : ℕ)) := by rw [htrav]
    _ = reconnectSparseCutsExt σ hinf (σ ((σ ^ (t - 1)) (c : ℕ))) := rfl
    _ = reconnectSparseCutsExt σ hinf (nextSparseCut σ c : ℕ) := by
      congr 1
      change σ ((σ ^ (t - 1)) (c : ℕ)) = (σ ^ (t : ℤ)) (c : ℕ)
      rw [zpow_natCast, ← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    _ = (reconnectSparseCuts σ hinf (nextSparseCut σ c) : ℕ) :=
      reconnectSparseCutsExt_apply_mem σ hinf _
    _ = (fusedSparseCutPerm σ hinf c : ℕ) := by rw [reconnectSparseCuts_next]

theorem sparselyRewiredPerm_sameCycle_fused (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) (c : sparseOrbitCuts σ) :
    Equiv.Perm.SameCycle (sparselyRewiredPerm σ hinf) (c : ℕ)
      (fusedSparseCutPerm σ hinf c : ℕ) := by
  refine ⟨(nextSparseCutTime σ c : ℤ), ?_⟩
  simpa only [zpow_natCast] using sparselyRewiredPerm_to_next_segment σ hinf c

theorem sparselyRewiredPerm_sameCycle_fused_zpow (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) (j : ℤ) (c : sparseOrbitCuts σ) :
    Equiv.Perm.SameCycle (sparselyRewiredPerm σ hinf) (c : ℕ)
      ((fusedSparseCutPerm σ hinf ^ j) c : ℕ) := by
  induction j using Int.induction_on with
  | zero => exact Equiv.Perm.SameCycle.rfl
  | succ j ih =>
      apply ih.trans
      have h := sparselyRewiredPerm_sameCycle_fused σ hinf
        ((fusedSparseCutPerm σ hinf ^ (j : ℤ)) c)
      have heq : fusedSparseCutPerm σ hinf
          ((fusedSparseCutPerm σ hinf ^ (j : ℤ)) c) =
          (fusedSparseCutPerm σ hinf ^ ((j : ℤ) + 1)) c := by
        calc
          _ = ((fusedSparseCutPerm σ hinf ^ (1 : ℤ)) *
                (fusedSparseCutPerm σ hinf ^ (j : ℤ))) c := by
            rw [zpow_one, Equiv.Perm.mul_apply]
          _ = (fusedSparseCutPerm σ hinf ^ ((1 : ℤ) + j)) c := by rw [zpow_add]
          _ = (fusedSparseCutPerm σ hinf ^ ((j : ℤ) + 1)) c := by
            congr 2
            omega
      rwa [heq] at h
  | pred j ih =>
      apply ih.trans
      have h := sparselyRewiredPerm_sameCycle_fused σ hinf
        ((fusedSparseCutPerm σ hinf ^ (-(j : ℤ) - 1)) c)
      have heq : fusedSparseCutPerm σ hinf
          ((fusedSparseCutPerm σ hinf ^ (-(j : ℤ) - 1)) c) =
          (fusedSparseCutPerm σ hinf ^ (-(j : ℤ))) c := by
        calc
          _ = ((fusedSparseCutPerm σ hinf ^ (1 : ℤ)) *
                (fusedSparseCutPerm σ hinf ^ (-(j : ℤ) - 1))) c := by
            rw [zpow_one, Equiv.Perm.mul_apply]
          _ = (fusedSparseCutPerm σ hinf ^ ((1 : ℤ) + (-(j : ℤ) - 1))) c := by
            rw [zpow_add]
          _ = (fusedSparseCutPerm σ hinf ^ (-(j : ℤ))) c := by
            congr 2
            omega
      rw [heq] at h
      exact h.symm

theorem sparselyRewiredPerm_sameCycle_cuts (σ : Equiv.Perm ℕ)
    (hinf : (sparseOrbitCuts σ).Infinite) (a b : sparseOrbitCuts σ) :
    Equiv.Perm.SameCycle (sparselyRewiredPerm σ hinf) (a : ℕ) (b : ℕ) := by
  obtain ⟨j, hj⟩ := fusedSparseCutPerm_sameCycle σ hinf a b
  rw [← hj]
  exact sparselyRewiredPerm_sameCycle_fused_zpow σ hinf j a

theorem sparseOrbitCuts_exists_forward (σ : Equiv.Perm ℕ) {x : ℕ}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) :
    ∃ k : ℕ, (σ ^ (k : ℤ)) x ∈ sparseOrbitCuts σ := by
  obtain ⟨k, _, hk⟩ := (sparseOrbitCuts_cofinal σ hinf).1 0
  exact ⟨k, hk⟩

/-- The first nonnegative time at which an infinite orbit reaches the sparse cut set. -/
noncomputable def firstSparseCutTime (σ : Equiv.Perm ℕ) (x : ℕ)
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) : ℕ := by
  classical
  exact Nat.find (sparseOrbitCuts_exists_forward σ hinf)

theorem firstSparseCutTime_spec (σ : Equiv.Perm ℕ) (x : ℕ)
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) :
    (σ ^ (firstSparseCutTime σ x hinf : ℤ)) x ∈ sparseOrbitCuts σ := by
  classical
  exact Nat.find_spec (sparseOrbitCuts_exists_forward σ hinf)

theorem sparselyRewiredPerm_sameCycle_some_cut (σ : Equiv.Perm ℕ)
    (hcuts : (sparseOrbitCuts σ).Infinite) {x : ℕ}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) :
    ∃ c : sparseOrbitCuts σ,
      Equiv.Perm.SameCycle (sparselyRewiredPerm σ hcuts) x (c : ℕ) := by
  classical
  let k := firstSparseCutTime σ x hinf
  let c : sparseOrbitCuts σ :=
    ⟨(σ ^ (k : ℤ)) x, firstSparseCutTime_spec σ x hinf⟩
  by_cases hk : k = 0
  · refine ⟨c, ?_⟩
    have hc : (c : ℕ) = x := by simp [c, hk]
    rw [hc]
  · let d : sparseOrbitCuts σ := reconnectSparseCuts σ hcuts c
    refine ⟨d, ⟨(k : ℤ), ?_⟩⟩
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hfree : ∀ r < k - 1, (σ ^ (r + 1)) x ∉ sparseOrbitCuts σ := by
      intro r hr hmem
      have hmin : k ≤ r + 1 := by
        apply Nat.find_min' (sparseOrbitCuts_exists_forward σ hinf)
        simpa only [zpow_natCast] using hmem
      omega
    have htrav :
        (sparselyRewiredPerm σ hcuts ^ (k - 1)) x = (σ ^ (k - 1)) x :=
      sparselyRewiredPerm_iterate_eq σ hcuts hfree
    rw [zpow_natCast, show k = (k - 1) + 1 by omega, pow_succ',
      Equiv.Perm.mul_apply, htrav]
    change sparselyRewiredPerm σ hcuts ((σ ^ (k - 1)) x) = (d : ℕ)
    rw [sparselyRewiredPerm_apply]
    have hnext : σ ((σ ^ (k - 1)) x) = (c : ℕ) := by
      change σ ((σ ^ (k - 1)) x) = (σ ^ (k : ℤ)) x
      rw [zpow_natCast, ← Equiv.Perm.mul_apply, ← pow_succ']
      congr 2
      omega
    rw [hnext, reconnectSparseCutsExt_apply_mem]

theorem sparselyRewiredPerm_connects_infinite_orbits (σ : Equiv.Perm ℕ)
    (hcuts : (sparseOrbitCuts σ).Infinite) {a b : ℕ}
    (ha : (Set.range fun j : ℤ => (σ ^ j) a).Infinite)
    (hb : (Set.range fun j : ℤ => (σ ^ j) b).Infinite) :
    ∃ j : ℤ, (sparselyRewiredPerm σ hcuts ^ j) a = b := by
  obtain ⟨ca, hca⟩ := sparselyRewiredPerm_sameCycle_some_cut σ hcuts ha
  obtain ⟨cb, hcb⟩ := sparselyRewiredPerm_sameCycle_some_cut σ hcuts hb
  exact hca.trans (sparselyRewiredPerm_sameCycle_cuts σ hcuts ca cb) |>.trans hcb.symm

theorem sparselyRewiredPerm_eq_of_finite_orbit (σ : Equiv.Perm ℕ)
    (hcuts : (sparseOrbitCuts σ).Infinite) {n : ℕ}
    (hfin : (Set.range fun j : ℤ => (σ ^ j) n).Finite) :
    sparselyRewiredPerm σ hcuts n = σ n := by
  apply sparselyRewiredPerm_apply_of_not_mem
  intro hmem
  have hinf := sparseOrbitCuts_only_infinite σ hmem
  have hinf' : (Set.range fun j : ℤ => (σ ^ j) ((σ ^ (1 : ℤ)) n)).Infinite := by
    simpa using hinf
  rw [perm_zpow_range_apply_zpow] at hinf'
  exact hinf' hfin

theorem sparselyRewiredPerm_ne_imp_image_mem (σ : Equiv.Perm ℕ)
    (hcuts : (sparseOrbitCuts σ).Infinite) {n : ℕ}
    (hne : sparselyRewiredPerm σ hcuts n ≠ σ n) :
    σ n ∈ sparseOrbitCuts σ := by
  by_contra h
  exact hne (sparselyRewiredPerm_apply_of_not_mem σ hcuts h)

theorem sparselyRewiredPerm_support_card_le_sqrt (σ : Equiv.Perm ℕ)
    (hstep : ∀ n, σ n ≤ 2 * n + 1) (hcuts : (sparseOrbitCuts σ).Infinite) (N : ℕ) :
    ((Finset.range N).filter fun n => sparselyRewiredPerm σ hcuts n ≠ σ n).card ≤
      Nat.sqrt (2 * N + 1) := by
  classical
  let D := (Finset.range N).filter fun n => sparselyRewiredPerm σ hcuts n ≠ σ n
  calc
    D.card = (D.image σ).card := (Finset.card_image_of_injective D σ.injective).symm
    _ ≤ ((Finset.range (Nat.sqrt (2 * N + 1))).image (sparseCutPoint σ)).card := by
      apply Finset.card_le_card
      intro y hy
      simp only [Finset.mem_image] at hy ⊢
      obtain ⟨n, hn, rfl⟩ := hy
      have hn' : n < N ∧ sparselyRewiredPerm σ hcuts n ≠ σ n := by
        simpa [D] using hn
      obtain ⟨q, _, hq⟩ :=
        sparselyRewiredPerm_ne_imp_image_mem σ hcuts hn'.2
      refine ⟨q, Finset.mem_range.mpr ?_, hq⟩
      have hsq : (q + 1) ^ 2 ≤ 2 * N + 1 := by
        calc
          (q + 1) ^ 2 ≤ sparseCutPoint σ q := sparseCutPoint_ge_square σ q
          _ = σ n := hq
          _ ≤ 2 * n + 1 := hstep n
          _ ≤ 2 * N + 1 := by omega
      have := Nat.le_sqrt'.mpr hsq
      omega
    _ ≤ Nat.sqrt (2 * N + 1) := by
      simpa using (Finset.card_image_le :
        ((Finset.range (Nat.sqrt (2 * N + 1))).image (sparseCutPoint σ)).card ≤
          (Finset.range (Nat.sqrt (2 * N + 1))).card)

theorem sqrt_two_mul_add_one_div_tendsto_zero :
    Filter.Tendsto (fun N : ℕ => Real.sqrt (2 * (N : ℝ) + 1) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  have hsqrt : Filter.Tendsto (fun N : ℕ => Real.sqrt (N : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hmajor : Filter.Tendsto
      (fun N : ℕ => Real.sqrt 3 * (Real.sqrt (N : ℝ))⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hsqrt.inv_tendsto_atTop
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    calc
      Real.sqrt (2 * (N : ℝ) + 1) / (N : ℝ) ≤
          Real.sqrt (3 * (N : ℝ)) / (N : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Real.sqrt_le_sqrt
        exact_mod_cast (show 2 * N + 1 ≤ 3 * N by omega)
      _ = Real.sqrt 3 * (Real.sqrt (N : ℝ) / (N : ℝ)) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 3)]
        ring
      _ = Real.sqrt 3 * (Real.sqrt (N : ℝ))⁻¹ := by
        rw [Real.sqrt_div_self]
  · exact hmajor

theorem sparselyRewiredPerm_support_density_zero (σ : Equiv.Perm ℕ)
    (hstep : ∀ n, σ n ≤ 2 * n + 1) (hcuts : (sparseOrbitCuts σ).Infinite) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n => sparselyRewiredPerm σ hcuts n ≠ σ n).card : ℝ) / N)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero
    (g := fun N : ℕ => Real.sqrt ((2 * N + 1 : ℕ) : ℝ) / (N : ℝ))
  · intro N
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro N
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    calc
      (((Finset.range N).filter fun n =>
          sparselyRewiredPerm σ hcuts n ≠ σ n).card : ℝ) ≤
          (Nat.sqrt (2 * N + 1) : ℝ) := by
        exact_mod_cast sparselyRewiredPerm_support_card_le_sqrt σ hstep hcuts N
      _ ≤ Real.sqrt ((2 * N + 1 : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      sqrt_two_mul_add_one_div_tendsto_zero

/-- A subset of the range of a sequence whose `n`th value is at least `(n + 1)²` has natural
density zero. -/
theorem sparse_range_density_zero (p : ℕ → Prop) [DecidablePred p] {f : ℕ → ℕ}
    (hsub : ∀ n, p n → n ∈ Set.range f) (hgrow : ∀ n, (n + 1) ^ 2 ≤ f n) :
    Filter.Tendsto
      (fun N : ℕ => (((Finset.range N).filter p).card : ℝ) / N)
      Filter.atTop (nhds 0) := by
  have hcard (N : ℕ) :
      ((Finset.range N).filter p).card ≤ Nat.sqrt N := by
    calc
      ((Finset.range N).filter p).card ≤
          ((Finset.range (Nat.sqrt N)).image f).card := by
        apply Finset.card_le_card
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_range] at hy
        obtain ⟨hyN, hy⟩ := hy
        obtain ⟨n, rfl⟩ := hsub y hy
        have hn : n + 1 ≤ Nat.sqrt N := Nat.le_sqrt'.mpr ((hgrow n).trans hyN.le)
        exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), rfl⟩
      _ ≤ Nat.sqrt N := by
        simpa using (Finset.card_image_le :
          ((Finset.range (Nat.sqrt N)).image f).card ≤ (Finset.range (Nat.sqrt N)).card)
  apply squeeze_zero (g := fun N : ℕ => Real.sqrt (N : ℝ) / N)
  · intro N
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro N
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    calc
      (((Finset.range N).filter p).card : ℝ) ≤ (Nat.sqrt N : ℝ) := by
        exact_mod_cast (hcard N)
      _ ≤ Real.sqrt (N : ℝ) := Real.nat_sqrt_le_real_sqrt
  · have hsqrt : Filter.Tendsto (fun N : ℕ => Real.sqrt (N : ℝ))
        Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    refine hsqrt.inv_tendsto_atTop.congr' ?_
    filter_upwards with N
    simp only [Pi.inv_apply, Real.sqrt_div_self]

/-- Every decidable subset of the selected cuts has natural density zero. -/
theorem sparseOrbitCuts_density_zero (σ : Equiv.Perm ℕ) (p : ℕ → Prop) [DecidablePred p]
    (hp : ∀ n, p n → n ∈ sparseOrbitCuts σ) :
    Filter.Tendsto (fun N : ℕ => (((Finset.range N).filter p).card : ℝ) / N)
      Filter.atTop (nhds 0) := by
  apply sparse_range_density_zero p _ (sparseCutPoint_ge_square σ)
  intro n hn
  obtain ⟨q, _, hq⟩ := hp n hn
  exact ⟨q, hq⟩

/-- A doubling-bounded permutation orbit crosses every sufficiently high annulus in both time
directions.  This is the quantitative input that lets the eventual cuts be chosen sparsely. -/
theorem exists_forward_backward_mem_Ico {σ : Equiv.Perm ℕ}
    (hstep : ∀ n, σ n ≤ 2 * n + 1 ∧ σ.symm n ≤ 2 * n + 1) {x Y : ℕ}
    (hinf : (Set.range fun j : ℤ => (σ ^ j) x).Infinite) (hxY : x < Y) :
    (∃ k : ℕ, (σ ^ k) x ∈ Set.Ico Y (2 * Y)) ∧
      ∃ k : ℕ, (σ.symm ^ k) x ∈ Set.Ico Y (2 * Y) := by
  have cross (π : Equiv.Perm ℕ) (hπ : ∀ n, π n ≤ 2 * n + 1)
      (hunbounded : ∃ k : ℕ, Y ≤ (π ^ k) x) :
      ∃ k : ℕ, (π ^ k) x ∈ Set.Ico Y (2 * Y) := by
    let k := Nat.find hunbounded
    have hkY : Y ≤ (π ^ k) x := Nat.find_spec hunbounded
    have hkpos : 0 < k := by
      by_contra hk
      have : k = 0 := Nat.eq_zero_of_not_pos hk
      rw [this] at hkY
      exact (Nat.not_le_of_lt hxY) hkY
    obtain ⟨l, hlk⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
    rw [hlk] at hkY
    have hl : (π ^ l) x < Y := by
      by_contra hlt
      have hle : Y ≤ (π ^ l) x := le_of_not_gt hlt
      have := Nat.find_min' hunbounded hle
      omega
    have hlt : (π ^ (l + 1)) x < 2 * Y := by
      rw [pow_succ', Equiv.Perm.mul_apply]
      have := hπ ((π ^ l) x)
      omega
    exact ⟨l + 1, hkY, hlt⟩
  constructor
  · apply cross σ (fun n => (hstep n).1)
    obtain ⟨k, hk⟩ := (exists_nat_iterate_gt hinf Y).1
    exact ⟨k, by simpa [zpow_natCast] using hk.le⟩
  · apply cross σ.symm (fun n => (hstep n).2)
    obtain ⟨k, hk⟩ := (exists_nat_iterate_gt hinf Y).2
    refine ⟨k, ?_⟩
    rw [zpow_neg, zpow_natCast] at hk
    change Y ≤ (σ⁻¹ ^ k) x
    simpa only [inv_pow] using hk.le

end CollatzMoonshot.Amusical
