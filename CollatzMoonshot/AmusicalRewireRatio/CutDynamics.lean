/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalRewireRatio.Splice

/-! The original successor relation between consecutive canonical scale cuts. -/

namespace CollatzMoonshot.Amusical

namespace ScaleCutIndex

theorem eq_of_level_rep_side_eq {i j : ScaleCutIndex} (hlevel : i.level = j.level)
    (hrep : i.rep = j.rep) (hside : i.side = j.side) : i = j := by
  cases i
  cases j
  simp_all

/-- Along one original orbit, backward cuts run down toward the representative and forward cuts
run away from it. -/
noncomputable def orbitSucc : Equiv.Perm ScaleCutIndex where
  toFun i :=
    match i.side with
    | .backward =>
        if h : i.rep < i.level then
          mkAt (i.level - 1) i.rep (by omega) i.rep_isInfinite .backward
        else
          mkAt i.level i.rep i.rep_le i.rep_isInfinite .forward
    | .forward =>
        mkAt (i.level + 1) i.rep (i.rep_le.trans (by omega))
          i.rep_isInfinite .forward
  invFun i :=
    match i.side with
    | .backward =>
        mkAt (i.level + 1) i.rep (i.rep_le.trans (by omega))
          i.rep_isInfinite .backward
    | .forward =>
        if h : i.rep < i.level then
          mkAt (i.level - 1) i.rep (by omega) i.rep_isInfinite .forward
        else
          mkAt i.level i.rep i.rep_le i.rep_isInfinite .backward
  left_inv i := by
    cases i with
    | mk level rep rep_le rep_isInfinite side =>
      cases side with
      | backward =>
        by_cases h : rep < level
        · simp only [h, ↓reduceDIte, mkAt]
          congr 1 <;> omega
        · have heq : rep = level := le_antisymm rep_le (not_lt.mp h)
          subst level
          simp [mkAt]
      | forward =>
        have h : rep < level + 1 := by omega
        simp only [h, ↓reduceDIte, mkAt]
        congr 1 <;> omega
  right_inv i := by
    cases i with
    | mk level rep rep_le rep_isInfinite side =>
      cases side with
      | backward =>
        have h : rep < level + 1 := by omega
        simp only [h, ↓reduceDIte, mkAt]
        congr 1 <;> omega
      | forward =>
        by_cases h : rep < level
        · simp only [h, ↓reduceDIte, mkAt]
          congr 1 <;> omega
        · have heq : rep = level := le_antisymm rep_le (not_lt.mp h)
          subst level
          simp [mkAt]

theorem orbitSucc_apply_backward_of_lt {i : ScaleCutIndex} (hside : i.side = .backward)
    (hlevel : i.rep < i.level) :
    orbitSucc i =
      mkAt (i.level - 1) i.rep (by omega) i.rep_isInfinite .backward := by
  simp [orbitSucc, hside, hlevel]

theorem orbitSucc_apply_backward_of_eq {i : ScaleCutIndex} (hside : i.side = .backward)
    (hlevel : i.rep = i.level) :
    orbitSucc i = mkAt i.level i.rep i.rep_le i.rep_isInfinite .forward := by
  simp [orbitSucc, hside, hlevel]

theorem orbitSucc_apply_forward {i : ScaleCutIndex} (hside : i.side = .forward) :
    orbitSucc i =
      mkAt (i.level + 1) i.rep (i.rep_le.trans (by omega))
        i.rep_isInfinite .forward := by
  simp [orbitSucc, hside]

theorem orbitSucc_rep (i : ScaleCutIndex) : (orbitSucc i).rep = i.rep := by
  cases hside : i.side with
  | backward =>
      by_cases hlevel : i.rep < i.level
      · rw [orbitSucc_apply_backward_of_lt hside hlevel]
        rfl
      · have heq : i.rep = i.level := le_antisymm i.rep_le (not_lt.mp hlevel)
        rw [orbitSucc_apply_backward_of_eq hside heq]
        rfl
  | forward =>
      rw [orbitSucc_apply_forward hside]
      rfl

/-- Integer orbit coordinate of a cut source, based at its canonical representative. -/
noncomputable def cutTime (i : ScaleCutIndex) : ℤ :=
  match i.side with
  | .backward => -(backwardPassage i.rep_infinite (scaleCutBase i.level) : ℤ)
  | .forward =>
      (forwardPassage i.rep_infinite (scaleCutBase i.level) - 1 : ℕ)

theorem source_eq_zpow_cutTime (i : ScaleCutIndex) :
    i.source = (amusicalNatPerm ^ i.cutTime) i.rep := by
  cases hside : i.side <;>
    simp [source, cut, cutTime, hside, backwardScaleCut, backwardCutSource,
      forwardScaleCut, forwardCutSource]

theorem natZpow_injective (i : ScaleCutIndex) :
    Function.Injective fun j : ℤ => (amusicalNatPerm ^ j) i.rep := by
  intro a b hab
  apply amusicalPerm_zpow_apply_injective_of_infinite i.rep_infinite
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hab
  simpa using hcast

theorem rep_eq_and_cutTime_eq_of_zpow_source_eq {i j : ScaleCutIndex} {n : ℤ}
    (hij : (amusicalNatPerm ^ n) i.source = j.source) :
    j.rep = i.rep ∧ j.cutTime = i.cutTime + n := by
  have hmem : (((amusicalNatPerm ^ n) i.source : ℕ) : ℤ) ∈
      amusicalOrbit (i.source : ℤ) := by
    refine ⟨n, ?_⟩
    exact (amusicalNatPerm_zpow_apply_cast n i.source).symm
  have horbit : amusicalOrbit (j.source : ℤ) = amusicalOrbit (i.source : ℤ) := by
    rw [← hij]
    exact amusicalOrbit_eq_of_mem hmem
  have hrep : j.rep = i.rep := by
    rw [← j.orbitMinNat_source, ← i.orbitMinNat_source]
    exact CollatzMoonshot.Obstructions.Amusical.orbitMinNat_eq_of_orbit_eq horbit
  refine ⟨hrep, ?_⟩
  apply i.natZpow_injective
  calc
    (amusicalNatPerm ^ j.cutTime) i.rep = j.source := by
      rw [← hrep, ← j.source_eq_zpow_cutTime]
    _ = (amusicalNatPerm ^ n) i.source := hij.symm
    _ = (amusicalNatPerm ^ (i.cutTime + n)) i.rep := by
      rw [i.source_eq_zpow_cutTime, ← Equiv.Perm.mul_apply, ← zpow_add]
      simp only [add_comm]

theorem cutTime_backward_neg {i : ScaleCutIndex} (hside : i.side = .backward) :
    i.cutTime < 0 := by
  have hpos := backwardPassage_pos i.rep_infinite (scaleCutBase i.level) i.rep_le_base
  simp [cutTime, hside, hpos]

theorem cutTime_forward_nonneg {i : ScaleCutIndex} (hside : i.side = .forward) :
    0 ≤ i.cutTime := by
  simp [cutTime, hside]

end ScaleCutIndex

theorem forwardPassage_strictMono_scaleCutBase {r k l : ℕ} (hr : IsInfiniteOrbitRep r)
    (hrk : r ≤ k) (hkl : k < l) :
    forwardPassage hr.2 (scaleCutBase k) < forwardPassage hr.2 (scaleCutBase l) := by
  have hrbase : r ≤ scaleCutBase k := hrk.trans (level_le_scaleCutBase k)
  have hcandidate := forwardPassage_gt hr.2 (scaleCutBase l)
  have hbase_lt : scaleCutBase k < scaleCutBase l := by
    have hsep := scaleCutBase_eight_mul_le hkl
    have hpos := scaleCutBase_pos k
    omega
  have hle : forwardPassage hr.2 (scaleCutBase k) ≤
      forwardPassage hr.2 (scaleCutBase l) :=
    Nat.find_min' (exists_forward_above hr.2 (scaleCutBase k)) <| by
      exact hbase_lt.trans hcandidate
  apply hle.lt_of_ne
  intro heq
  let i : ScaleCutIndex := ⟨k, r, hrk, hr, .forward⟩
  let j : ScaleCutIndex := ⟨l, r, hrk.trans hkl.le, hr, .forward⟩
  have htarget := ScaleCutIndex.target_lt_of_level_lt (i := i) (j := j) hkl
  simp only [ScaleCutIndex.target, ScaleCutIndex.cut, i, j, forwardScaleCut,
    forwardCutTarget, heq] at htarget
  omega

theorem backwardPassage_strictMono_scaleCutBase {r k l : ℕ} (hr : IsInfiniteOrbitRep r)
    (hrk : r ≤ k) (hkl : k < l) :
    backwardPassage hr.2 (scaleCutBase k) < backwardPassage hr.2 (scaleCutBase l) := by
  have hcandidate := backwardPassage_gt hr.2 (scaleCutBase l)
  have hbase_lt : scaleCutBase k < scaleCutBase l := by
    have hsep := scaleCutBase_eight_mul_le hkl
    have hpos := scaleCutBase_pos k
    omega
  have hle : backwardPassage hr.2 (scaleCutBase k) ≤
      backwardPassage hr.2 (scaleCutBase l) :=
    Nat.find_min' (exists_backward_above hr.2 (scaleCutBase k)) <| by
      exact hbase_lt.trans hcandidate
  apply hle.lt_of_ne
  intro heq
  let i : ScaleCutIndex := ⟨k, r, hrk, hr, .backward⟩
  let j : ScaleCutIndex := ⟨l, r, hrk.trans hkl.le, hr, .backward⟩
  have hsource := ScaleCutIndex.source_lt_of_level_lt (i := i) (j := j) hkl
  simp only [ScaleCutIndex.source, ScaleCutIndex.cut, i, j, backwardScaleCut,
    backwardCutSource, heq] at hsource
  omega

namespace ScaleCutIndex

theorem cutTime_lt_of_forward_level_lt {i j : ScaleCutIndex}
    (hi : i.side = .forward) (hj : j.side = .forward) (hrep : j.rep = i.rep)
    (hlevel : i.level < j.level) : i.cutTime < j.cutTime := by
  have hpass := forwardPassage_strictMono_scaleCutBase i.rep_isInfinite i.rep_le hlevel
  have hipos := forwardPassage_pos i.rep_infinite (scaleCutBase i.level) i.rep_le_base
  have hjpos := forwardPassage_pos j.rep_infinite (scaleCutBase j.level) j.rep_le_base
  simp only [cutTime, hi, hj]
  simp only [hrep] at hpass ⊢
  push_cast
  omega

theorem cutTime_lt_of_backward_level_lt {i j : ScaleCutIndex}
    (hi : i.side = .backward) (hj : j.side = .backward) (hrep : j.rep = i.rep)
    (hlevel : i.level < j.level) : j.cutTime < i.cutTime := by
  have hpass := backwardPassage_strictMono_scaleCutBase i.rep_isInfinite i.rep_le hlevel
  simp only [cutTime, hi, hj]
  simp only [hrep] at hpass ⊢
  push_cast
  omega

/-- Canonical cut times on one original orbit have no value strictly between a cut and its
structural successor. -/
theorem cutTime_le_or_orbitSucc_cutTime_le (i j : ScaleCutIndex)
    (hrep : j.rep = i.rep) :
    j.cutTime ≤ i.cutTime ∨ (orbitSucc i).cutTime ≤ j.cutTime := by
  cases hi : i.side with
  | backward =>
      by_cases hilevel : i.rep < i.level
      · rw [orbitSucc_apply_backward_of_lt hi hilevel]
        cases hj : j.side with
        | backward =>
            rcases lt_trichotomy j.level i.level with hjlt | hjeq | hjgt
            · have hjle : j.level ≤ i.level - 1 := by omega
              rcases lt_or_eq_of_le hjle with hjlt' | hjeq'
              · right
                exact (cutTime_lt_of_backward_level_lt hj rfl
                  (by simpa [mkAt] using hrep.symm)
                  hjlt').le
              · right
                have heq : j = mkAt (i.level - 1) i.rep (by omega)
                    i.rep_isInfinite .backward := by
                  apply eq_of_level_rep_side_eq <;> simp_all [mkAt]
                rw [heq]
            · left
              have heq : j = i := by
                apply eq_of_level_rep_side_eq <;> simp_all
              rw [heq]
            · left
              exact (cutTime_lt_of_backward_level_lt hi hj hrep hjgt).le
        | forward =>
            right
            have hneg : (mkAt (i.level - 1) i.rep (by omega)
                i.rep_isInfinite .backward).cutTime < 0 := cutTime_backward_neg rfl
            have hnonneg := cutTime_forward_nonneg hj
            omega
      · have hieq : i.rep = i.level := le_antisymm i.rep_le (not_lt.mp hilevel)
        rw [orbitSucc_apply_backward_of_eq hi hieq]
        cases hj : j.side with
        | backward =>
            left
            have hjrep := j.rep_le
            have hle : i.level ≤ j.level := by omega
            rcases lt_or_eq_of_le hle with hlt | heq
            · exact (cutTime_lt_of_backward_level_lt hi hj hrep hlt).le
            · have hji : j = i := by
                apply eq_of_level_rep_side_eq <;> simp_all
              rw [hji]
        | forward =>
            right
            have hjrep := j.rep_le
            have hle : i.level ≤ j.level := by omega
            rcases lt_or_eq_of_le hle with hlt | heq
            · exact (cutTime_lt_of_forward_level_lt
                (i := mkAt i.level i.rep i.rep_le i.rep_isInfinite .forward) (j := j)
                rfl hj (by simpa [mkAt] using hrep) hlt).le
            · have hji : j = mkAt i.level i.rep i.rep_le i.rep_isInfinite .forward := by
                apply eq_of_level_rep_side_eq <;> simp_all [mkAt]
              rw [hji]
  | forward =>
      rw [orbitSucc_apply_forward hi]
      cases hj : j.side with
      | backward =>
          left
          have hneg := cutTime_backward_neg hj
          have hnonneg := cutTime_forward_nonneg hi
          omega
      | forward =>
          by_cases hjle : j.level ≤ i.level
          · left
            rcases lt_or_eq_of_le hjle with hlt | heq
            · exact (cutTime_lt_of_forward_level_lt hj hi hrep.symm hlt).le
            · have hji : j = i := by
                apply eq_of_level_rep_side_eq <;> simp_all
              rw [hji]
          · right
            have hsucc : i.level + 1 ≤ j.level := by omega
            rcases lt_or_eq_of_le hsucc with hlt | heq
            · exact (cutTime_lt_of_forward_level_lt
                (i := mkAt (i.level + 1) i.rep (i.rep_le.trans (by omega))
                  i.rep_isInfinite .forward) (j := j) rfl hj
                (by simpa [mkAt] using hrep) hlt).le
            · have hji : j = mkAt (i.level + 1) i.rep
                  (i.rep_le.trans (by omega)) i.rep_isInfinite .forward := by
                apply eq_of_level_rep_side_eq <;> simp_all [mkAt]
              rw [hji]

/-- Number of original successor steps from a cut source to the next canonical cut source on
the same orbit. -/
noncomputable def orbitSegmentLength (i : ScaleCutIndex) : ℕ :=
  match i.side with
  | .backward =>
      if h : i.rep < i.level then
        backwardPassage i.rep_infinite (scaleCutBase i.level) -
          backwardPassage i.rep_infinite (scaleCutBase (i.level - 1))
      else
        backwardPassage i.rep_infinite (scaleCutBase i.level) +
          forwardPassage i.rep_infinite (scaleCutBase i.level) - 1
  | .forward =>
      forwardPassage i.rep_infinite (scaleCutBase (i.level + 1)) -
        forwardPassage i.rep_infinite (scaleCutBase i.level)

theorem orbitSegmentLength_pos (i : ScaleCutIndex) : 0 < i.orbitSegmentLength := by
  cases hside : i.side with
  | backward =>
      by_cases hlevel : i.rep < i.level
      · have hprev : i.rep ≤ i.level - 1 := by omega
        have hstrict := backwardPassage_strictMono_scaleCutBase i.rep_isInfinite hprev
          (show i.level - 1 < i.level by omega)
        simp only [orbitSegmentLength, hside, hlevel, ↓reduceDIte]
        omega
      · have hback := backwardPassage_pos i.rep_infinite (scaleCutBase i.level)
          i.rep_le_base
        have hfwd := forwardPassage_pos i.rep_infinite (scaleCutBase i.level)
          i.rep_le_base
        simp only [orbitSegmentLength, hside, hlevel, ↓reduceDIte]
        omega
  | forward =>
      have hstrict : forwardPassage i.rep_infinite (scaleCutBase i.level) <
          forwardPassage i.rep_infinite (scaleCutBase (i.level + 1)) := by
        simpa only [Nat.succ_eq_add_one] using
          forwardPassage_strictMono_scaleCutBase i.rep_isInfinite i.rep_le
            (Nat.lt_succ_self i.level)
      simp only [orbitSegmentLength, hside]
      omega

theorem cutTime_add_orbitSegmentLength (i : ScaleCutIndex) :
    i.cutTime + i.orbitSegmentLength = (orbitSucc i).cutTime := by
  cases hside : i.side with
  | backward =>
      by_cases hlevel : i.rep < i.level
      · have hprev : i.rep ≤ i.level - 1 := by omega
        have hstrict := backwardPassage_strictMono_scaleCutBase i.rep_isInfinite hprev
          (show i.level - 1 < i.level by omega)
        rw [orbitSucc_apply_backward_of_lt hside hlevel]
        simp only [cutTime, mkAt, orbitSegmentLength, hside, hlevel, ↓reduceDIte]
        push_cast
        omega
      · have heq : i.rep = i.level := le_antisymm i.rep_le (not_lt.mp hlevel)
        have hback := backwardPassage_pos i.rep_infinite (scaleCutBase i.level)
          i.rep_le_base
        have hfwd := forwardPassage_pos i.rep_infinite (scaleCutBase i.level)
          i.rep_le_base
        rw [orbitSucc_apply_backward_of_eq hside heq]
        simp only [cutTime, mkAt, orbitSegmentLength, hside, hlevel, ↓reduceDIte]
        push_cast
        omega
  | forward =>
      have hstrict : forwardPassage i.rep_infinite (scaleCutBase i.level) <
          forwardPassage i.rep_infinite (scaleCutBase (i.level + 1)) := by
        simpa only [Nat.succ_eq_add_one] using
          forwardPassage_strictMono_scaleCutBase i.rep_isInfinite i.rep_le
            (Nat.lt_succ_self i.level)
      have hcur := forwardPassage_pos i.rep_infinite (scaleCutBase i.level)
        i.rep_le_base
      have hnext := forwardPassage_pos i.rep_infinite (scaleCutBase (i.level + 1))
        (i.rep_le.trans <| (Nat.le_succ i.level).trans <| level_le_scaleCutBase _)
      rw [orbitSucc_apply_forward hside]
      simp only [cutTime, mkAt, orbitSegmentLength, hside]
      push_cast
      omega

/-- Strictly inside a canonical orbit segment, no point is another canonical cut source. -/
theorem zpow_source_notMem_range_of_lt (i : ScaleCutIndex) {n : ℕ} (hnpos : 0 < n)
    (hnlt : n < i.orbitSegmentLength) :
    (amusicalNatPerm ^ (n : ℤ)) i.source ∉ Set.range source := by
  rintro ⟨j, hj⟩
  have hcoord := rep_eq_and_cutTime_eq_of_zpow_source_eq (i := i) (j := j) hj.symm
  have hgap := cutTime_le_or_orbitSucc_cutTime_le i j hcoord.1
  rw [hcoord.2, ← i.cutTime_add_orbitSegmentLength] at hgap
  have hnpos' : (0 : ℤ) < n := by exact_mod_cast hnpos
  have hnlt' : (n : ℤ) < i.orbitSegmentLength := by exact_mod_cast hnlt
  omega

theorem zpow_orbitSegmentLength_source (i : ScaleCutIndex) :
    (amusicalNatPerm ^ (i.orbitSegmentLength : ℤ)) i.source = (orbitSucc i).source := by
  rw [i.source_eq_zpow_cutTime]
  rw [← Equiv.Perm.mul_apply, ← zpow_add]
  rw [add_comm, cutTime_add_orbitSegmentLength]
  rw [← orbitSucc_rep i, ← source_eq_zpow_cutTime]

/-- After the initial rewired edge, a source follows the untouched interior of the selected
canonical segment. -/
theorem rewired_zpow_source_eq (p : Equiv.Perm ScaleCutIndex) (i : ScaleCutIndex)
    (n : ℕ) (hnpos : 0 < n) (hnle : n ≤ (p i).orbitSegmentLength) :
    ((amusicalNatPerm * scaleCutSourcePerm p) ^ (n : ℤ)) i.source =
      (amusicalNatPerm ^ (n : ℤ)) (p i).source := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hnzero : n = 0
      · subst n
        change (amusicalNatPerm * scaleCutSourcePerm p) i.source =
          amusicalNatPerm (p i).source
        rw [scaleCut_rewired_apply, (p i).map_source]
      · have hnpos' : 0 < n := Nat.pos_of_ne_zero hnzero
        have hnlt : n < (p i).orbitSegmentLength := by omega
        have hnot := (p i).zpow_source_notMem_range_of_lt hnpos' hnlt
        have hih := ih hnpos' hnlt.le
        rw [show ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) by omega]
        rw [zpow_add, zpow_add, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, zpow_one,
          zpow_one, hih, Equiv.Perm.mul_apply,
          scaleCutSourcePerm_apply_of_not_range p hnot]

/-- The induced transition on canonical cut sources is `orbitSucc ∘ p`. -/
theorem rewired_zpow_orbitSegmentLength_source (p : Equiv.Perm ScaleCutIndex)
    (i : ScaleCutIndex) :
    ((amusicalNatPerm * scaleCutSourcePerm p) ^ ((p i).orbitSegmentLength : ℤ))
        i.source = (orbitSucc (p i)).source := by
  rw [rewired_zpow_source_eq p i _ (p i).orbitSegmentLength_pos le_rfl]
  exact (p i).zpow_orbitSegmentLength_source

end ScaleCutIndex

end CollatzMoonshot.Amusical
