/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalRewireRatio.Passage

/-! Scale-indexed cuts and the quantitative interface for permuting their sources. -/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- A canonical representative of an infinite nonnegative amusical orbit. -/
def IsInfiniteOrbitRep (r : ℕ) : Prop :=
  orbitMinNat (r : ℤ) = r ∧ (amusicalOrbit (r : ℤ)).Infinite

theorem orbitMinNat_isInfiniteOrbitRep {x : ℕ} (hx : (amusicalOrbit (x : ℤ)).Infinite) :
    IsInfiniteOrbitRep (orbitMinNat (x : ℤ)) := by
  let r := orbitMinNat (x : ℤ)
  have hmem : (r : ℤ) ∈ amusicalOrbit (x : ℤ) := orbitMinNat_mem (Int.natCast_nonneg x)
  have horbit : amusicalOrbit (r : ℤ) = amusicalOrbit (x : ℤ) :=
    amusicalOrbit_eq_of_mem hmem
  exact ⟨by simpa only [r] using orbitMinNat_eq_of_orbit_eq horbit, horbit.symm ▸ hx⟩

/-- The two cuts used for each active orbit and scale. -/
inductive ScaleCutSide
  | backward
  | forward
  deriving DecidableEq

/-- Scale `k` uses height `8^(k+1)`.  Consecutive scales are separated by a factor of eight. -/
def scaleCutBase (k : ℕ) : ℕ := 8 ^ (k + 1)

theorem scaleCutBase_pos (k : ℕ) : 0 < scaleCutBase k := by
  simp [scaleCutBase]

theorem scaleCutBase_eight_mul (k : ℕ) :
    8 * scaleCutBase k = scaleCutBase (k + 1) := by
  simp [scaleCutBase, pow_succ, Nat.mul_comm]

theorem scaleCutBase_eight_mul_le {k l : ℕ} (hkl : k < l) :
    8 * scaleCutBase k ≤ scaleCutBase l := by
  rw [scaleCutBase_eight_mul]
  exact pow_le_pow_right' (by omega) (by omega)

theorem level_le_scaleCutBase (k : ℕ) : k ≤ scaleCutBase k := by
  have htwo : k < 2 ^ k := k.lt_two_pow_self
  have hbase : 2 ^ k ≤ 8 ^ k := Nat.pow_le_pow_left (by omega) k
  have hexp : 8 ^ k ≤ 8 ^ (k + 1) := pow_le_pow_right' (by omega) (by omega)
  exact htwo.le.trans (hbase.trans hexp)

/-- An orbit representative active at level `level`, together with a side of its orbit. -/
structure ScaleCutIndex where
  level : ℕ
  rep : ℕ
  rep_le : rep ≤ level
  rep_isInfinite : IsInfiniteOrbitRep rep
  side : ScaleCutSide

namespace ScaleCutIndex

theorem rep_le_base (i : ScaleCutIndex) : i.rep ≤ scaleCutBase i.level :=
  i.rep_le.trans (level_le_scaleCutBase i.level)

/-- The first-passage cut selected by an index. -/
noncomputable def cut (i : ScaleCutIndex) : AmusicalScaleCut (scaleCutBase i.level) :=
  match i.side with
  | .backward =>
      backwardScaleCut i.rep_isInfinite.2 (scaleCutBase i.level) i.rep_le_base
  | .forward =>
      forwardScaleCut i.rep_isInfinite.2 (scaleCutBase i.level) i.rep_le_base

/-- The source of a scale-indexed cut edge. -/
noncomputable def source (i : ScaleCutIndex) : ℕ := i.cut.source

/-- The target of a scale-indexed cut edge. -/
noncomputable def target (i : ScaleCutIndex) : ℕ := i.cut.target

theorem map_source (i : ScaleCutIndex) : amusicalNatPerm i.source = i.target :=
  i.cut.map_source

theorem rep_min (i : ScaleCutIndex) : orbitMinNat (i.rep : ℤ) = i.rep := by
  exact i.rep_isInfinite.1

theorem rep_infinite (i : ScaleCutIndex) : (amusicalOrbit (i.rep : ℤ)).Infinite := by
  exact i.rep_isInfinite.2

theorem source_le_base_of_side_eq_forward {i : ScaleCutIndex} (hi : i.side = .forward) :
    i.source ≤ scaleCutBase i.level := by
  simp only [source, cut, hi]
  exact forwardCutSource_le i.rep_infinite _ i.rep_le_base

theorem base_lt_source_of_side_eq_backward {i : ScaleCutIndex} (hi : i.side = .backward) :
    scaleCutBase i.level < i.source := by
  simp only [source, cut, hi]
  exact backwardCutSource_gt i.rep_infinite _

theorem source_lt_of_level_lt {i j : ScaleCutIndex} (hij : i.level < j.level) :
    i.source < j.source := by
  exact AmusicalScaleCut.source_lt_of_eight_mul_le i.cut j.cut
    (scaleCutBase_pos i.level) (scaleCutBase_eight_mul_le hij)

theorem target_lt_of_level_lt {i j : ScaleCutIndex} (hij : i.level < j.level) :
    i.target < j.target := by
  exact AmusicalScaleCut.target_lt_of_eight_mul_le i.cut j.cut
    (scaleCutBase_pos i.level) (scaleCutBase_eight_mul_le hij)

theorem source_mem_orbit (i : ScaleCutIndex) :
    (i.source : ℤ) ∈ amusicalOrbit (i.rep : ℤ) := by
  cases hside : i.side with
  | backward =>
      refine ⟨-(backwardPassage i.rep_infinite (scaleCutBase i.level) : ℤ), ?_⟩
      change (amusicalPerm ^ (-(backwardPassage i.rep_infinite
        (scaleCutBase i.level) : ℤ))) (i.rep : ℤ) = (i.source : ℤ)
      rw [← amusicalNatPerm_zpow_apply_cast]
      simp only [source, cut, hside, backwardScaleCut, backwardCutSource]
  | forward =>
      refine ⟨((forwardPassage i.rep_infinite (scaleCutBase i.level) - 1 : ℕ) : ℤ), ?_⟩
      change (amusicalPerm ^ ((forwardPassage i.rep_infinite
        (scaleCutBase i.level) - 1 : ℕ) : ℤ)) (i.rep : ℤ) = (i.source : ℤ)
      rw [← amusicalNatPerm_zpow_apply_cast]
      simp only [source, cut, hside, forwardScaleCut, forwardCutSource]

theorem source_orbit (i : ScaleCutIndex) :
    amusicalOrbit (i.source : ℤ) = amusicalOrbit (i.rep : ℤ) :=
  amusicalOrbit_eq_of_mem i.source_mem_orbit

theorem source_orbit_infinite (i : ScaleCutIndex) :
    (amusicalOrbit (i.source : ℤ)).Infinite := by
  rw [i.source_orbit]
  exact i.rep_infinite

theorem orbitMinNat_source (i : ScaleCutIndex) : orbitMinNat (i.source : ℤ) = i.rep := by
  rw [orbitMinNat_eq_of_orbit_eq i.source_orbit]
  exact i.rep_min

theorem level_eq_of_source_eq {i j : ScaleCutIndex} (hij : i.source = j.source) :
    i.level = j.level := by
  rcases lt_trichotomy i.level j.level with hlt | heq | hgt
  · exact ((i.source_lt_of_level_lt hlt).ne hij).elim
  · exact heq
  · exact ((j.source_lt_of_level_lt hgt).ne hij.symm).elim

theorem rep_eq_of_source_eq {i j : ScaleCutIndex} (hij : i.source = j.source) :
    i.rep = j.rep := by
  rw [← i.orbitMinNat_source, ← j.orbitMinNat_source, hij]

theorem side_eq_of_source_eq {i j : ScaleCutIndex} (hij : i.source = j.source) :
    i.side = j.side := by
  have hlevel := level_eq_of_source_eq hij
  by_contra hside
  cases hi : i.side <;> cases hj : j.side
  · exact hside (hi.trans hj.symm)
  · have hisource := base_lt_source_of_side_eq_backward (i := i) hi
    have hjsource := source_le_base_of_side_eq_forward (i := j) hj
    have hbase : scaleCutBase i.level = scaleCutBase j.level := congrArg scaleCutBase hlevel
    omega
  · have hisource := source_le_base_of_side_eq_forward (i := i) hi
    have hjsource := base_lt_source_of_side_eq_backward (i := j) hj
    have hbase : scaleCutBase i.level = scaleCutBase j.level := congrArg scaleCutBase hlevel
    omega
  · exact hside (hi.trans hj.symm)

theorem source_injective : Function.Injective source := by
  intro i j hij
  have hlevel := level_eq_of_source_eq hij
  have hrep := rep_eq_of_source_eq hij
  have hside := side_eq_of_source_eq hij
  cases i
  cases j
  simp_all

/-- Scale cuts embed into the natural numbers by their pairwise distinct sources. -/
noncomputable def sourceEmbedding : ScaleCutIndex ↪ ℕ :=
  ⟨source, source_injective⟩

theorem three_mul_two_pow_le_two_mul_base (k : ℕ) :
    3 * 2 ^ k ≤ 2 * scaleCutBase k := by
  have hbase : 2 ^ k ≤ 8 ^ k := Nat.pow_le_pow_left (by omega) k
  have hmul : 3 * 2 ^ k ≤ 3 * 8 ^ k := Nat.mul_le_mul_left 3 hbase
  apply hmul.trans
  simp only [scaleCutBase, pow_succ]
  omega

theorem two_pow_level_le_source (i : ScaleCutIndex) : 2 ^ i.level ≤ i.source := by
  have hbase := three_mul_two_pow_le_two_mul_base i.level
  have hsource := i.cut.source_lower
  change 2 ^ i.level ≤ i.cut.source
  omega

theorem level_le_log_of_source_lt {i : ScaleCutIndex} {N : ℕ} (hiN : i.source < N) :
    i.level ≤ Nat.log 2 N := by
  apply Nat.le_log_of_pow_le (by omega)
  exact i.two_pow_level_le_source.trans hiN.le

end ScaleCutIndex

/-- Extend a permutation of scale-cut indices by the identity away from cut sources. -/
noncomputable def scaleCutSourcePerm (p : Equiv.Perm ScaleCutIndex) : Equiv.Perm ℕ :=
  p.viaEmbedding ScaleCutIndex.sourceEmbedding

theorem scaleCutSourcePerm_apply (p : Equiv.Perm ScaleCutIndex) (i : ScaleCutIndex) :
    scaleCutSourcePerm p i.source = (p i).source := by
  exact Equiv.Perm.viaEmbedding_apply p ScaleCutIndex.sourceEmbedding i

theorem scaleCutSourcePerm_apply_of_not_range (p : Equiv.Perm ScaleCutIndex) {n : ℕ}
    (hn : n ∉ Set.range ScaleCutIndex.source) : scaleCutSourcePerm p n = n := by
  exact Equiv.Perm.viaEmbedding_apply_of_notMem p ScaleCutIndex.sourceEmbedding n hn

theorem scaleCutSourcePerm_fixed_finite (p : Equiv.Perm ScaleCutIndex) (n : ℕ)
    (hn : (amusicalOrbit (n : ℤ)).Finite) : scaleCutSourcePerm p n = n := by
  apply scaleCutSourcePerm_apply_of_not_range
  rintro ⟨i, rfl⟩
  exact i.source_orbit_infinite hn

theorem scaleCutSourcePerm_target_ratio (p : Equiv.Perm ScaleCutIndex)
    (hlevel : ∀ i, (p i).level = i.level) (n : ℕ) :
    amusicalNatPerm (scaleCutSourcePerm p n) ≤ 3 * amusicalNatPerm n + 3 ∧
      amusicalNatPerm n ≤ 3 * amusicalNatPerm (scaleCutSourcePerm p n) + 3 := by
  classical
  by_cases hn : n ∈ Set.range ScaleCutIndex.source
  · obtain ⟨i, rfl⟩ := hn
    rw [scaleCutSourcePerm_apply, i.map_source, (p i).map_source]
    have h := hlevel i
    have hpupper := (p i).cut.target_upper
    have hplower := (p i).cut.target_lower
    have hiupper := i.cut.target_upper
    have hilower := i.cut.target_lower
    have hbase : scaleCutBase (p i).level = scaleCutBase i.level := congrArg scaleCutBase h
    change 2 * (p i).target ≤ 3 * scaleCutBase (p i).level at hpupper
    change 3 * scaleCutBase (p i).level ≤ 4 * (p i).target + 1 at hplower
    change 2 * i.target ≤ 3 * scaleCutBase i.level at hiupper
    change 3 * scaleCutBase i.level ≤ 4 * i.target + 1 at hilower
    change (p i).target ≤ 3 * i.target + 3 ∧ i.target ≤ 3 * (p i).target + 3
    constructor <;> omega
  · rw [scaleCutSourcePerm_apply_of_not_range p hn]
    omega

private noncomputable def scaleCutSourceIndex? (n : ℕ) : Option ScaleCutIndex := by
  classical
  exact if h : n ∈ Set.range ScaleCutIndex.source then some (Classical.choose h) else none

private theorem scaleCutSourceIndex?_spec {n : ℕ} {i : ScaleCutIndex}
    (hi : scaleCutSourceIndex? n = some i) : i.source = n := by
  classical
  unfold scaleCutSourceIndex? at hi
  by_cases h : n ∈ Set.range ScaleCutIndex.source
  · rw [dif_pos h] at hi
    have hchosen : (Classical.choose h).source = n := Classical.choose_spec h
    have hei : Classical.choose h = i := Option.some.inj hi
    rwa [hei] at hchosen
  · rw [dif_neg h] at hi
    simp at hi

private theorem scaleCutSourceIndex?_isSome {n : ℕ}
    (hn : n ∈ Set.range ScaleCutIndex.source) : ∃ i, scaleCutSourceIndex? n = some i := by
  classical
  unfold scaleCutSourceIndex?
  simp only [dif_pos hn, Option.some.injEq, exists_eq']

private noncomputable def scaleCutSourceCode (n : ℕ) : Option ((ℕ × ℕ) × ScaleCutSide) :=
  (scaleCutSourceIndex? n).map fun i => ((i.level, i.rep), i.side)

private theorem scaleCutSourceCode_injective_on_range :
    Set.InjOn scaleCutSourceCode (Set.range ScaleCutIndex.source) := by
  intro n hn m hm hcode
  obtain ⟨i, hi⟩ := scaleCutSourceIndex?_isSome hn
  obtain ⟨j, hj⟩ := scaleCutSourceIndex?_isSome hm
  have hfields : ((i.level, i.rep), i.side) = ((j.level, j.rep), j.side) := by
    simpa [scaleCutSourceCode, hi, hj] using hcode
  have hij : i = j := by
    cases i
    cases j
    simp_all
  rw [← scaleCutSourceIndex?_spec hi, ← scaleCutSourceIndex?_spec hj, hij]

private def scaleCutSourceCodesUpTo (L : ℕ) : Finset (Option ((ℕ × ℕ) × ScaleCutSide)) :=
  (((Finset.range (L + 1)).product (Finset.range (L + 1))).product
    {.backward, .forward}).image some

private theorem scaleCutSourceCodesUpTo_card (L : ℕ) :
    (scaleCutSourceCodesUpTo L).card = 2 * (L + 1) ^ 2 := by
  classical
  rw [scaleCutSourceCodesUpTo, Finset.card_image_of_injective _
    (fun (_a _b : ((ℕ × ℕ) × ScaleCutSide)) hab => Option.some.inj hab)]
  calc
    ((((Finset.range (L + 1)).product (Finset.range (L + 1))).product
        {ScaleCutSide.backward, ScaleCutSide.forward}).card) =
        ((Finset.range (L + 1)).product (Finset.range (L + 1))).card *
          ({ScaleCutSide.backward, ScaleCutSide.forward} : Finset ScaleCutSide).card :=
      Finset.card_product _ _
    _ = ((Finset.range (L + 1)).card * (Finset.range (L + 1)).card) * 2 := by
      exact congrArg₂ (fun a b : ℕ => a * b) (Finset.card_product _ _) (by decide)
    _ = 2 * (L + 1) ^ 2 := by simp [pow_two]; ring

theorem scaleCutSourcePerm_moved_card (p : Equiv.Perm ScaleCutIndex) :
    ∃ C : ℕ, ∀ N : ℕ,
      ((Finset.range N).filter fun n => scaleCutSourcePerm p n ≠ n).card ≤
        C * (Nat.log 2 N + 1) ^ 2 := by
  classical
  refine ⟨2, fun N => ?_⟩
  let moved := (Finset.range N).filter fun n => scaleCutSourcePerm p n ≠ n
  let codes := scaleCutSourceCodesUpTo (Nat.log 2 N)
  have hmoved_range : (moved : Set ℕ) ⊆ Set.range ScaleCutIndex.source := by
    intro n hn
    have hn' : n ∈ moved := hn
    rw [Finset.mem_filter] at hn'
    by_contra hnr
    exact hn'.2 (scaleCutSourcePerm_apply_of_not_range p hnr)
  have hmaps : Set.MapsTo scaleCutSourceCode (moved : Set ℕ) codes := by
    intro n hn
    have hnrange := hmoved_range hn
    obtain ⟨i, hi⟩ := scaleCutSourceIndex?_isSome hnrange
    have hisource := scaleCutSourceIndex?_spec hi
    have hn' : n ∈ moved := hn
    rw [Finset.mem_filter] at hn'
    have hnlt : n < N := Finset.mem_range.mp hn'.1
    have hlevel : i.level ≤ Nat.log 2 N :=
      i.level_le_log_of_source_lt (hisource.trans_lt hnlt)
    have hrep : i.rep ≤ Nat.log 2 N := i.rep_le.trans hlevel
    have hside : i.side = .backward ∨ i.side = .forward := by
      cases i.side <;> simp
    simp [codes, scaleCutSourceCodesUpTo, scaleCutSourceCode, hi, hlevel, hrep, hside]
  calc
    moved.card ≤ codes.card := Finset.card_le_card_of_injOn scaleCutSourceCode hmaps
      (scaleCutSourceCode_injective_on_range.mono hmoved_range)
    _ = 2 * (Nat.log 2 N + 1) ^ 2 := scaleCutSourceCodesUpTo_card _

end CollatzMoonshot.Amusical
