/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindow

/-!
# Orbit minima of the amusical permutation have upper density below `1/20`

`windowMinDensity 200` bounds the upper density of orbit minima by `δ₂₀₀ = fwdSurv 200 *
bwdSurv 200 = 0.0498876…`, just under `1/20` (the conjectured density is `0.049780`).  The
pattern sums have `2^200` terms, so `windowDensity_two_hundred_lt` groups surviving words by step
and number of marked letters, proves that these semantic counts obey a linear-size integer lattice
recurrence, and then checks the resulting exact inequality in the kernel.
-/

namespace CollatzMoonshot.Amusical

open Classical in
/-- Split a sum over words by the last letter.  Unlike direct reduction of a
`Fintype` of functions, this identity scales inductively and is the entry point
for connecting the word sums to the lattice rows. -/
theorem sum_bool_snoc {n : ℕ} (f : (Fin (n + 1) → Bool) → ℚ) :
    ∑ w, f w = ∑ b : Bool, ∑ u : Fin n → Bool, f (Fin.snoc u b) := by
  refine ((Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool))
    (fun x => f (Fin.snoc x.2 x.1)) f (fun _ => rfl)).symm).trans ?_
  exact Fintype.sum_prod_type _

/-! ## A linear-size lattice computation

The rows below store integer numerators.  At time `t`, entry `o` is the total
weight of surviving prefixes with exactly `o` marked letters.  Forward letters
both have weight one (the common denominator is `2^t`); backward unmarked and
marked letters have weights one and two (common denominator `3^t`).  Passing
the preceding entry explicitly makes one row step linear rather than rebuilding
the preceding row at every output coordinate during kernel reduction. -/

def fwdLatticeStep (t o prev : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
      (if 2 ^ (t + 1 + o) < 3 ^ (t + 1) then x + prev else 0) ::
        fwdLatticeStep t (o + 1) x xs

def bwdLatticeStep (t o prev : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
      (if 3 ^ (t + 1) < 2 ^ (t + 1 + o) then x + 2 * prev else 0) ::
        bwdLatticeStep t (o + 1) x xs

def fwdLatticeRow : ℕ → List ℕ
  | 0 => [1]
  | t + 1 => fwdLatticeStep t 0 0 (fwdLatticeRow t ++ [0])

def bwdLatticeRow : ℕ → List ℕ
  | 0 => [1]
  | t + 1 => bwdLatticeStep t 0 0 (bwdLatticeRow t ++ [0])

def fwdLatticeNum (L : ℕ) : ℕ := (fwdLatticeRow L).sum
def bwdLatticeNum (L : ℕ) : ℕ := (bwdLatticeRow L).sum

theorem fwdLatticeStep_length (t o prev : ℕ) (xs : List ℕ) :
    (fwdLatticeStep t o prev xs).length = xs.length := by
  induction xs generalizing o prev with
  | nil => rfl
  | cons x xs ih => simp [fwdLatticeStep, ih]

theorem bwdLatticeStep_length (t o prev : ℕ) (xs : List ℕ) :
    (bwdLatticeStep t o prev xs).length = xs.length := by
  induction xs generalizing o prev with
  | nil => rfl
  | cons x xs ih => simp [bwdLatticeStep, ih]

/-- A coordinate of a forward lattice step only uses the two adjacent
coordinates of the preceding row.  The explicit `prev` argument is the
coordinate immediately to the left of the input list. -/
theorem fwdLatticeStep_getD (t o prev k : ℕ) (xs : List ℕ) (hk : k < xs.length) :
    (fwdLatticeStep t o prev xs).getD k 0 =
      if 2 ^ (t + 1 + (o + k)) < 3 ^ (t + 1) then
        xs.getD k 0 + if k = 0 then prev else xs.getD (k - 1) 0
      else 0 := by
  induction xs generalizing o prev k with
  | nil => simp at hk
  | cons x xs ih =>
      cases k with
      | zero => simp [fwdLatticeStep]
      | succ k =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
          rw [fwdLatticeStep, List.getD_cons_succ, ih (o := o + 1) (prev := x) k hk]
          cases k <;> simp [Nat.add_left_comm, Nat.add_comm]

/-- Backward lattice coordinates satisfy the analogous adjacent-coordinate
recurrence, with weight two on a newly marked letter. -/
theorem bwdLatticeStep_getD (t o prev k : ℕ) (xs : List ℕ) (hk : k < xs.length) :
    (bwdLatticeStep t o prev xs).getD k 0 =
      if 3 ^ (t + 1) < 2 ^ (t + 1 + (o + k)) then
        xs.getD k 0 + 2 * (if k = 0 then prev else xs.getD (k - 1) 0)
      else 0 := by
  induction xs generalizing o prev k with
  | nil => simp at hk
  | cons x xs ih =>
      cases k with
      | zero => simp [bwdLatticeStep]
      | succ k =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
          rw [bwdLatticeStep, List.getD_cons_succ, ih (o := o + 1) (prev := x) k hk]
          cases k <;> simp [Nat.add_left_comm, Nat.add_comm]

private theorem getD_append_zero (xs : List ℕ) (k : ℕ) (hk : k ≤ xs.length) :
    (xs ++ [0]).getD k 0 = xs.getD k 0 := by
  rcases hk.lt_or_eq with hk | rfl
  · exact List.getD_append xs [0] 0 k hk
  · simp

/-- Each computed row has exactly one coordinate for every possible mark count. -/
theorem fwdLatticeRow_length (t : ℕ) : (fwdLatticeRow t).length = t + 1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [fwdLatticeRow, fwdLatticeStep_length, ih]

/-- Each computed row has exactly one coordinate for every possible mark count. -/
theorem bwdLatticeRow_length (t : ℕ) : (bwdLatticeRow t).length = t + 1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [bwdLatticeRow, bwdLatticeStep_length, ih]

/-- Coordinate form of the forward row recurrence. -/
theorem fwdLatticeRow_succ_getD (t o : ℕ) (ho : o ≤ t + 1) :
    (fwdLatticeRow (t + 1)).getD o 0 =
      if 2 ^ (t + 1 + o) < 3 ^ (t + 1) then
        (fwdLatticeRow t).getD o 0 +
          if o = 0 then 0 else (fwdLatticeRow t).getD (o - 1) 0
      else 0 := by
  rw [fwdLatticeRow, fwdLatticeStep_getD]
  · rw [getD_append_zero _ o]
    · by_cases h : o = 0
      · simp [h]
      · have hp : o - 1 ≤ (fwdLatticeRow t).length := by
          rw [fwdLatticeRow_length]
          omega
        rw [getD_append_zero _ _ hp]
        simp
    · simpa [fwdLatticeRow_length] using ho
  · simpa [fwdLatticeRow_length] using Nat.lt_succ_of_le ho

/-- Coordinate form of the backward row recurrence. -/
theorem bwdLatticeRow_succ_getD (t o : ℕ) (ho : o ≤ t + 1) :
    (bwdLatticeRow (t + 1)).getD o 0 =
      if 3 ^ (t + 1) < 2 ^ (t + 1 + o) then
        (bwdLatticeRow t).getD o 0 +
          2 * (if o = 0 then 0 else (bwdLatticeRow t).getD (o - 1) 0)
      else 0 := by
  rw [bwdLatticeRow, bwdLatticeStep_getD]
  · rw [getD_append_zero _ o]
    · by_cases h : o = 0
      · simp [h]
      · have hp : o - 1 ≤ (bwdLatticeRow t).length := by
          rw [bwdLatticeRow_length]
          omega
        rw [getD_append_zero _ _ hp]
        simp
    · simpa [bwdLatticeRow_length] using ho
  · simpa [bwdLatticeRow_length] using Nat.lt_succ_of_le ho

/-! ## Semantic identification of the lattice rows

The following counts retain the branch word semantics but group surviving words
by their number of marked letters.  Splitting a word at its last letter gives
exactly the adjacent-coordinate recurrences above. -/

def latticeMarked {L : ℕ} (w : Fin L → Bool) : ℕ :=
  (Finset.univ.filter fun i => w i = true).card

def latticePrefixMarked {L : ℕ} (w : Fin L → Bool) (t : ℕ) : ℕ :=
  (Finset.univ.filter fun i => i.val < t ∧ w i = true).card

theorem latticeMarked_snoc {n : ℕ} (u : Fin n → Bool) (b : Bool) :
    latticeMarked (Fin.snoc u b) = latticeMarked u + if b then 1 else 0 := by
  simp only [latticeMarked, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  cases b <;> simp

theorem latticePrefixMarked_snoc_of_le {n t : ℕ} (u : Fin n → Bool) (b : Bool)
    (ht : t ≤ n) :
    latticePrefixMarked (Fin.snoc u b) t = latticePrefixMarked u t := by
  simp only [latticePrefixMarked, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp [ht]

theorem latticePrefixMarked_snoc_full {n : ℕ} (u : Fin n → Bool) (b : Bool) :
    latticePrefixMarked (Fin.snoc u b) (n + 1) =
      latticeMarked u + if b then 1 else 0 := by
  simp only [latticePrefixMarked, latticeMarked, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  cases b <;> simp

def FwdLatticeGood {L : ℕ} (w : Fin L → Bool) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ L → 2 ^ (t + latticePrefixMarked w t) < 3 ^ t

def BwdLatticeGood {L : ℕ} (w : Fin L → Bool) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ L → 3 ^ t < 2 ^ (t + latticePrefixMarked w t)

theorem fwdLatticeGood_snoc {n : ℕ} (u : Fin n → Bool) (b : Bool) :
    FwdLatticeGood (Fin.snoc u b) ↔ FwdLatticeGood u ∧
      2 ^ (n + 1 + (latticeMarked u + if b then 1 else 0)) < 3 ^ (n + 1) := by
  constructor
  · intro h
    constructor
    · intro t ht1 htn
      simpa only [latticePrefixMarked_snoc_of_le u b htn] using h t ht1 (by omega)
    · simpa only [latticePrefixMarked_snoc_full] using h (n + 1) (by omega) (by omega)
  · rintro ⟨hu, hlast⟩ t ht1 ht
    rcases lt_or_eq_of_le ht with htlt | rfl
    · rw [latticePrefixMarked_snoc_of_le u b (by omega)]
      exact hu t ht1 (by omega)
    · simpa only [latticePrefixMarked_snoc_full] using hlast

theorem bwdLatticeGood_snoc {n : ℕ} (u : Fin n → Bool) (b : Bool) :
    BwdLatticeGood (Fin.snoc u b) ↔ BwdLatticeGood u ∧
      3 ^ (n + 1) < 2 ^ (n + 1 + (latticeMarked u + if b then 1 else 0)) := by
  constructor
  · intro h
    constructor
    · intro t ht1 htn
      simpa only [latticePrefixMarked_snoc_of_le u b htn] using h t ht1 (by omega)
    · simpa only [latticePrefixMarked_snoc_full] using h (n + 1) (by omega) (by omega)
  · rintro ⟨hu, hlast⟩ t ht1 ht
    rcases lt_or_eq_of_le ht with htlt | rfl
    · rw [latticePrefixMarked_snoc_of_le u b (by omega)]
      exact hu t ht1 (by omega)
    · simpa only [latticePrefixMarked_snoc_full] using hlast

open Classical in
theorem sum_bool_snoc_nat {n : ℕ} (f : (Fin (n + 1) → Bool) → ℕ) :
    ∑ w, f w = ∑ b : Bool, ∑ u : Fin n → Bool, f (Fin.snoc u b) := by
  refine ((Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool))
    (fun x => f (Fin.snoc x.2 x.1)) f (fun _ => rfl)).symm).trans ?_
  exact Fintype.sum_prod_type _

noncomputable def fwdLatticeCount (t o : ℕ) : ℕ := by
  classical
  exact ∑ w : Fin t → Bool, if FwdLatticeGood w ∧ latticeMarked w = o then 1 else 0

noncomputable def bwdLatticeCount (t o : ℕ) : ℕ := by
  classical
  exact ∑ w : Fin t → Bool,
    if BwdLatticeGood w ∧ latticeMarked w = o then 2 ^ latticeMarked w else 0

theorem latticeMarked_le {t : ℕ} (w : Fin t → Bool) : latticeMarked w ≤ t := by
  unfold latticeMarked
  calc
    _ ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_filter_le _ _
    _ = t := Fintype.card_fin t

theorem fwdLatticeCount_eq_zero_of_lt {t o : ℕ} (h : t < o) :
    fwdLatticeCount t o = 0 := by
  classical
  unfold fwdLatticeCount
  apply Finset.sum_eq_zero
  intro w _
  rw [if_neg]
  rintro ⟨_, rfl⟩
  exact (not_le_of_gt h) (latticeMarked_le w)

theorem bwdLatticeCount_eq_zero_of_lt {t o : ℕ} (h : t < o) :
    bwdLatticeCount t o = 0 := by
  classical
  unfold bwdLatticeCount
  apply Finset.sum_eq_zero
  intro w _
  rw [if_neg]
  rintro ⟨_, rfl⟩
  exact (not_le_of_gt h) (latticeMarked_le w)

theorem fwdLatticeGood_marked_snoc_false {n o : ℕ} (u : Fin n → Bool) :
    (FwdLatticeGood (Fin.snoc u false) ∧ latticeMarked (Fin.snoc u false) = o) ↔
      (FwdLatticeGood u ∧ latticeMarked u = o) ∧
        2 ^ (n + 1 + o) < 3 ^ (n + 1) := by
  rw [fwdLatticeGood_snoc, latticeMarked_snoc]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  constructor
  · rintro ⟨⟨hu, hg⟩, ho⟩
    subst o
    exact ⟨⟨hu, rfl⟩, hg⟩
  · rintro ⟨⟨hu, ho⟩, hg⟩
    subst o
    exact ⟨⟨hu, hg⟩, rfl⟩

theorem fwdLatticeGood_marked_snoc_true {n o : ℕ} (u : Fin n → Bool) :
    (FwdLatticeGood (Fin.snoc u true) ∧ latticeMarked (Fin.snoc u true) = o) ↔
      o ≠ 0 ∧ (FwdLatticeGood u ∧ latticeMarked u = o - 1) ∧
        2 ^ (n + 1 + o) < 3 ^ (n + 1) := by
  rw [fwdLatticeGood_snoc, latticeMarked_snoc]
  simp only [↓reduceIte]
  constructor
  · rintro ⟨⟨hu, hg⟩, ho⟩
    refine ⟨by omega, ⟨hu, by omega⟩, ?_⟩
    rwa [ho] at hg
  · rintro ⟨ho0, ⟨hu, ho⟩, hg⟩
    have heq : latticeMarked u + 1 = o := by omega
    refine ⟨⟨hu, ?_⟩, heq⟩
    rwa [heq]

theorem bwdLatticeGood_marked_snoc_false {n o : ℕ} (u : Fin n → Bool) :
    (BwdLatticeGood (Fin.snoc u false) ∧ latticeMarked (Fin.snoc u false) = o) ↔
      (BwdLatticeGood u ∧ latticeMarked u = o) ∧
        3 ^ (n + 1) < 2 ^ (n + 1 + o) := by
  rw [bwdLatticeGood_snoc, latticeMarked_snoc]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  constructor
  · rintro ⟨⟨hu, hg⟩, ho⟩
    subst o
    exact ⟨⟨hu, rfl⟩, hg⟩
  · rintro ⟨⟨hu, ho⟩, hg⟩
    subst o
    exact ⟨⟨hu, hg⟩, rfl⟩

theorem bwdLatticeGood_marked_snoc_true {n o : ℕ} (u : Fin n → Bool) :
    (BwdLatticeGood (Fin.snoc u true) ∧ latticeMarked (Fin.snoc u true) = o) ↔
      o ≠ 0 ∧ (BwdLatticeGood u ∧ latticeMarked u = o - 1) ∧
        3 ^ (n + 1) < 2 ^ (n + 1 + o) := by
  rw [bwdLatticeGood_snoc, latticeMarked_snoc]
  simp only [↓reduceIte]
  constructor
  · rintro ⟨⟨hu, hg⟩, ho⟩
    refine ⟨by omega, ⟨hu, by omega⟩, ?_⟩
    rwa [ho] at hg
  · rintro ⟨ho0, ⟨hu, ho⟩, hg⟩
    have heq : latticeMarked u + 1 = o := by omega
    refine ⟨⟨hu, ?_⟩, heq⟩
    rwa [heq]

theorem fwdLatticeCount_succ (t o : ℕ) :
    fwdLatticeCount (t + 1) o =
      if 2 ^ (t + 1 + o) < 3 ^ (t + 1) then
        fwdLatticeCount t o + if o = 0 then 0 else fwdLatticeCount t (o - 1)
      else 0 := by
  classical
  unfold fwdLatticeCount
  rw [sum_bool_snoc_nat, Fintype.sum_bool]
  by_cases hg : 2 ^ (t + 1 + o) < 3 ^ (t + 1)
  · rw [if_pos hg]
    by_cases ho : o = 0
    · subst o
      simp only [if_pos, add_zero]
      simp_rw [fwdLatticeGood_marked_snoc_true, fwdLatticeGood_marked_snoc_false]
      simp [hg]
    · rw [if_neg ho]
      simp_rw [fwdLatticeGood_marked_snoc_true, fwdLatticeGood_marked_snoc_false]
      simp [hg, ho]
      omega
  · rw [if_neg hg]
    simp_rw [fwdLatticeGood_marked_snoc_true, fwdLatticeGood_marked_snoc_false]
    simp [hg]

theorem bwdLatticeCount_succ (t o : ℕ) :
    bwdLatticeCount (t + 1) o =
      if 3 ^ (t + 1) < 2 ^ (t + 1 + o) then
        bwdLatticeCount t o + 2 * (if o = 0 then 0 else bwdLatticeCount t (o - 1))
      else 0 := by
  classical
  unfold bwdLatticeCount
  rw [sum_bool_snoc_nat, Fintype.sum_bool]
  by_cases hg : 3 ^ (t + 1) < 2 ^ (t + 1 + o)
  · rw [if_pos hg]
    by_cases ho : o = 0
    · subst o
      simp only [if_pos, mul_zero, add_zero]
      simp_rw [bwdLatticeGood_marked_snoc_true, bwdLatticeGood_marked_snoc_false]
      simp_rw [latticeMarked_snoc]
      simp [hg]
    · rw [if_neg ho]
      simp_rw [bwdLatticeGood_marked_snoc_true, bwdLatticeGood_marked_snoc_false]
      simp_rw [latticeMarked_snoc]
      simp only [hg, and_true, if_true]
      simp [ho, pow_succ]
      have hfactor :
          (∑ x : Fin t → Bool,
              if BwdLatticeGood x ∧ latticeMarked x = o - 1 then
                2 ^ latticeMarked x * 2 else 0) =
            2 * ∑ x : Fin t → Bool,
              if BwdLatticeGood x ∧ latticeMarked x = o - 1 then
                2 ^ latticeMarked x else 0 := by
        calc
          _ = ∑ x : Fin t → Bool,
              (if BwdLatticeGood x ∧ latticeMarked x = o - 1 then
                2 ^ latticeMarked x else 0) * 2 := by
                apply Finset.sum_congr rfl
                intro x _
                split_ifs <;> simp
          _ = (∑ x : Fin t → Bool,
              if BwdLatticeGood x ∧ latticeMarked x = o - 1 then
                2 ^ latticeMarked x else 0) * 2 := by
                rw [Finset.sum_mul]
          _ = _ := by omega
      rw [hfactor]
      omega
  · rw [if_neg hg]
    simp_rw [bwdLatticeGood_marked_snoc_true, bwdLatticeGood_marked_snoc_false]
    simp_rw [latticeMarked_snoc]
    simp [hg]

theorem fwdLatticeCount_eq_row (t o : ℕ) :
    fwdLatticeCount t o = (fwdLatticeRow t).getD o 0 := by
  induction t generalizing o with
  | zero =>
      by_cases ho : o = 0
      · subst o
        have hgood (w : Fin 0 → Bool) : FwdLatticeGood w := by
          intro t ht1 ht0
          omega
        simp [fwdLatticeCount, latticeMarked, fwdLatticeRow, hgood]
      · rw [fwdLatticeCount_eq_zero_of_lt (by omega), List.getD_eq_default]
        simp [fwdLatticeRow]
        omega
  | succ t ih =>
      by_cases ho : o ≤ t + 1
      · rw [fwdLatticeCount_succ, fwdLatticeRow_succ_getD t o ho, ih o, ih (o - 1)]
      · rw [fwdLatticeCount_eq_zero_of_lt (by omega), List.getD_eq_default]
        rw [fwdLatticeRow_length]
        omega

theorem bwdLatticeCount_eq_row (t o : ℕ) :
    bwdLatticeCount t o = (bwdLatticeRow t).getD o 0 := by
  induction t generalizing o with
  | zero =>
      by_cases ho : o = 0
      · subst o
        have hgood (w : Fin 0 → Bool) : BwdLatticeGood w := by
          intro t ht1 ht0
          omega
        simp [bwdLatticeCount, latticeMarked, bwdLatticeRow, hgood]
      · rw [bwdLatticeCount_eq_zero_of_lt (by omega), List.getD_eq_default]
        simp [bwdLatticeRow]
        omega
  | succ t ih =>
      by_cases ho : o ≤ t + 1
      · rw [bwdLatticeCount_succ, bwdLatticeRow_succ_getD t o ho, ih o, ih (o - 1)]
      · rw [bwdLatticeCount_eq_zero_of_lt (by omega), List.getD_eq_default]
        rw [bwdLatticeRow_length]
        omega

theorem sum_getD_eq_sum (xs : List ℕ) :
    (∑ i ∈ Finset.range xs.length, xs.getD i 0) = xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_zero,
        List.getD_cons_succ, List.sum_cons, ih]
      omega

theorem fwdLatticeNum_eq_sum_count (L : ℕ) :
    fwdLatticeNum L = ∑ o ∈ Finset.range (L + 1), fwdLatticeCount L o := by
  unfold fwdLatticeNum
  rw [← sum_getD_eq_sum (fwdLatticeRow L), fwdLatticeRow_length]
  apply Finset.sum_congr rfl
  intro o _
  exact (fwdLatticeCount_eq_row L o).symm

theorem bwdLatticeNum_eq_sum_count (L : ℕ) :
    bwdLatticeNum L = ∑ o ∈ Finset.range (L + 1), bwdLatticeCount L o := by
  unfold bwdLatticeNum
  rw [← sum_getD_eq_sum (bwdLatticeRow L), bwdLatticeRow_length]
  apply Finset.sum_congr rfl
  intro o _
  exact (bwdLatticeCount_eq_row L o).symm

open Classical in
theorem sum_fwdLatticeCount (L : ℕ) :
    (∑ o ∈ Finset.range (L + 1), fwdLatticeCount L o) =
      ∑ w : Fin L → Bool, if FwdLatticeGood w then 1 else 0 := by
  classical
  unfold fwdLatticeCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : FwdLatticeGood w
  · simp [hw, latticeMarked_le w]
  · simp [hw]

open Classical in
theorem sum_bwdLatticeCount (L : ℕ) :
    (∑ o ∈ Finset.range (L + 1), bwdLatticeCount L o) =
      ∑ w : Fin L → Bool,
        if BwdLatticeGood w then 2 ^ latticeMarked w else 0 := by
  classical
  unfold bwdLatticeCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : BwdLatticeGood w
  · simp [hw, latticeMarked_le w]
  · simp [hw]

open Classical in
/-- The forward lattice numerator is exactly the word survival probability
after clearing its common denominator. -/
theorem fwdSurv_mul_two (L : ℕ) :
    (2 : ℚ) ^ L * fwdSurv L = (fwdLatticeNum L : ℚ) := by
  have hcount : fwdLatticeNum L =
      ∑ w : Fin L → Bool, if FwdLatticeGood w then 1 else 0 :=
    (fwdLatticeNum_eq_sum_count L).trans (sum_fwdLatticeCount L)
  calc
    (2 : ℚ) ^ L * fwdSurv L =
        ∑ w : Fin L → Bool, if FwdLatticeGood w then 1 else 0 := by
      unfold fwdSurv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      have hiff :
          (∀ t : ℕ, 1 ≤ t → t ≤ L →
            2 ^ (t + ((Finset.univ.filter fun i : Fin L =>
              i.val < t ∧ w i = true).card)) < 3 ^ t) ↔ FwdLatticeGood w := by
        rfl
      by_cases hw : FwdLatticeGood w
      · rw [if_pos hw, if_pos (hiff.mpr hw), ← mul_pow]
        norm_num
      · rw [if_neg hw, if_neg (fun h => hw (hiff.mp h))]
        simp
    _ = (fwdLatticeNum L : ℚ) := by exact_mod_cast hcount.symm

open Classical in
/-- The backward lattice numerator is exactly the word survival probability
after clearing its common denominator. -/
theorem bwdSurv_mul_three (L : ℕ) :
    (3 : ℚ) ^ L * bwdSurv L = (bwdLatticeNum L : ℚ) := by
  have hcount : bwdLatticeNum L =
      ∑ w : Fin L → Bool,
        if BwdLatticeGood w then 2 ^ latticeMarked w else 0 :=
    (bwdLatticeNum_eq_sum_count L).trans (sum_bwdLatticeCount L)
  rw [bwdSurv_mul]
  rw [count_bwdGood]
  exact_mod_cast (show
      (∑ w : Fin L → Bool,
        if BwdGood L w then
          2 ^ (Finset.univ.filter fun i : Fin L => w i = true).card else 0) =
        bwdLatticeNum L by
    calc
      _ = ∑ w : Fin L → Bool,
          if BwdLatticeGood w then 2 ^ latticeMarked w else 0 := by
        apply Finset.sum_congr rfl
        intro w _
        have hiff : BwdGood L w ↔ BwdLatticeGood w := by rfl
        by_cases hw : BwdLatticeGood w
        · rw [if_pos hw, if_pos (hiff.mpr hw)]
          rfl
        · rw [if_neg hw, if_neg (fun h => hw (hiff.mp h))]
      _ = bwdLatticeNum L := hcount.symm)

/-- The lattice recurrence reproduces the four small window-density controls. -/
theorem latticeDensity_values :
    fwdLatticeNum 1 * bwdLatticeNum 1 * 3 = 2 ^ 1 * 3 ^ 1 ∧
      fwdLatticeNum 2 * bwdLatticeNum 2 * 9 = 2 * (2 ^ 2 * 3 ^ 2) ∧
      fwdLatticeNum 3 * bwdLatticeNum 3 * 6 = 2 ^ 3 * 3 ^ 3 ∧
      fwdLatticeNum 4 * bwdLatticeNum 4 * 27 = 4 * (2 ^ 4 * 3 ^ 4) := by
  decide +kernel

/-- Exact kernel evaluation of the 200-step lattice, identified above with the
word-sum definitions. -/
theorem latticeDensity_two_hundred_lt :
    20 * fwdLatticeNum 200 * bwdLatticeNum 200 < 2 ^ 200 * 3 ^ 200 := by
  decide +kernel

/-- **`δ₂₀₀ < 1/20`** (proved 2026-10-13 by treadmill from
`KICKOFF-2026-10-13-amusical-bound.md`; axiom-clean).  Exact value `0.04988761510…`
(`scripts/amusical/window.py`-style lattice computation, 2026-10-13). -/
theorem windowDensity_two_hundred_lt : fwdSurv 200 * bwdSurv 200 < 1 / 20 := by
  have hf := fwdSurv_mul_two 200
  have hb := bwdSurv_mul_three 200
  have hf' : fwdSurv 200 = (fwdLatticeNum 200 : ℚ) / (2 : ℚ) ^ 200 := by
    apply (eq_div_iff (by positivity)).2
    simpa only [mul_comm] using hf
  have hb' : bwdSurv 200 = (bwdLatticeNum 200 : ℚ) / (3 : ℚ) ^ 200 := by
    apply (eq_div_iff (by positivity)).2
    simpa only [mul_comm] using hb
  rw [hf', hb', div_mul_div_comm]
  apply (div_lt_div_iff₀ (by positivity) (by norm_num)).2
  simp only [one_mul]
  have h :
      (20 : ℚ) * (fwdLatticeNum 200 : ℚ) * (bwdLatticeNum 200 : ℚ) <
        (2 : ℚ) ^ 200 * (3 : ℚ) ^ 200 := by
    exact_mod_cast latticeDensity_two_hundred_lt
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

open Classical in
/-- **Orbit minima have upper density below `1/20`**: eventually fewer than `X/20` of
`0, …, X-1` are orbit minima. -/
theorem orbitMin_density_lt_one_twentieth : ∀ᶠ X : ℕ in Filter.atTop,
    (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X < 1 / 20 := by
  set δ : ℝ := ((fwdSurv 200 * bwdSurv 200 : ℚ) : ℝ)
  have hδ : δ < 1 / 20 := by
    have h := windowDensity_two_hundred_lt
    have : ((fwdSurv 200 * bwdSurv 200 : ℚ) : ℝ) < ((1 / 20 : ℚ) : ℝ) := Rat.cast_lt.2 h
    simpa [δ] using this
  filter_upwards [orbitMin_density_le 200 (by linarith : (0 : ℝ) < (1 / 20 - δ) / 2)] with X hX
  linarith

end CollatzMoonshot.Amusical
