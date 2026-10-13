/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Strict cyclic minima

The elementary cyclic-minimum lemma used in strict Sparre--Andersen arguments.  If every two
prefix sums are distinct and the total sum is positive, rotating immediately after a least
proper prefix produces a word whose every nonempty prefix has positive sum.
-/

namespace CollatzMoonshot

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- Every nonempty prefix of `l` has strictly positive sum. -/
def StrictlyPositivePrefixes (l : List α) : Prop :=
  ∀ t : ℕ, 0 < t → t ≤ l.length → 0 < (l.take t).sum

/-- If every nonempty contiguous block has nonzero sum, then all prefix sums are distinct. -/
theorem prefixSums_ne_of_blocks_ne_zero (l : List α)
    (hblock : ∀ i n : ℕ, 0 < n → i + n ≤ l.length →
      ((l.drop i).take n).sum ≠ 0) :
    ∀ i j : ℕ, i < j → j ≤ l.length → (l.take i).sum ≠ (l.take j).sum := by
  intro i j hij hj heq
  have hsum : (l.take j).sum =
      (l.take i).sum + ((l.drop i).take (j - i)).sum := by
    rw [← List.sum_append, ← List.take_add]
    congr 2
    omega
  have hz : ((l.drop i).take (j - i)).sum = 0 := by
    apply add_left_cancel (a := (l.take i).sum)
    simpa using (heq.trans hsum).symm
  exact hblock i (j - i) (by omega) (by omega) hz

/-- A positive-total list with distinct prefix sums has a cyclic rotation all of whose
nonempty prefix sums are positive. -/
theorem exists_rotate_strictlyPositivePrefixes (l : List α)
    (hsum : 0 < l.sum)
    (htie : ∀ i j : ℕ, i < j → j ≤ l.length → (l.take i).sum ≠ (l.take j).sum) :
    ∃ r < l.length, StrictlyPositivePrefixes (l.rotate r) := by
  have hn : 0 < l.length := by
    cases l with
    | nil => simp at hsum
    | cons => simp
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image (Finset.range l.length)
    (fun i => (l.take i).sum) ⟨0, Finset.mem_range.mpr hn⟩
  have hrn : r < l.length := Finset.mem_range.mp hr
  refine ⟨r, hrn, ?_⟩
  intro t ht htlen
  have htlen' : t ≤ l.length := by simpa using htlen
  rw [List.rotate_eq_drop_append_take hrn.le]
  by_cases hfirst : t ≤ l.length - r
  · have htake : (List.take t (l.drop r ++ l.take r)).sum =
        ((l.drop r).take t).sum := by
      rw [List.take_append]
      simp [List.length_drop, Nat.sub_eq_zero_of_le hfirst]
    rw [htake]
    have hjle : r + t ≤ l.length := by omega
    have hsplit : (l.take (r + t)).sum =
        (l.take r).sum + ((l.drop r).take t).sum := by
      rw [List.take_add, List.sum_append]
    have hlt : (l.take r).sum < (l.take (r + t)).sum := by
      by_cases hj : r + t < l.length
      · exact lt_of_le_of_ne
          (hmin (r + t) (Finset.mem_range.mpr hj))
          (htie r (r + t) (by omega) hjle)
      · have hr0 : (l.take r).sum ≤ 0 := by
          simpa using hmin 0 (Finset.mem_range.mpr hn)
        have hj_eq : r + t = l.length := by omega
        simpa [hj_eq, List.take_length] using lt_of_le_of_lt hr0 hsum
    rw [hsplit] at hlt
    exact (lt_add_iff_pos_right _).mp hlt
  · have hdrop_le : (l.drop r).length ≤ t := by
      simp only [List.length_drop]
      omega
    let q := t - (l.length - r)
    have hq : q ≤ r := by
      dsimp [q]
      omega
    have hqmem : q ∈ Finset.range l.length := by
      apply Finset.mem_range.mpr
      omega
    have htake : (List.take t (l.drop r ++ l.take r)).sum =
        (l.drop r).sum + (l.take q).sum := by
      rw [List.take_append, List.take_of_length_le hdrop_le, List.sum_append]
      simp only [List.length_drop]
      rw [show t - (l.length - r) = q by rfl, List.take_take, min_eq_left hq]
    rw [htake]
    have hbase : 0 < (l.take r).sum + (l.drop r).sum := by
      simpa [List.sum_take_add_sum_drop] using hsum
    have hle : (l.take r).sum + (l.drop r).sum ≤
        (l.take q).sum + (l.drop r).sum := by
      simpa [add_comm] using add_le_add_right (hmin q hqmem) (l.drop r).sum
    exact lt_of_lt_of_le hbase (by simpa [add_comm] using hle)

/-- Under the no-tie hypothesis, a list has positive total sum exactly when some cyclic
rotation has all nonempty prefix sums positive. -/
theorem sum_pos_iff_exists_rotate_strictlyPositivePrefixes (l : List α)
    (htie : ∀ i j : ℕ, i < j → j ≤ l.length → (l.take i).sum ≠ (l.take j).sum) :
    0 < l.sum ↔ ∃ r < l.length, StrictlyPositivePrefixes (l.rotate r) := by
  constructor
  · intro h
    exact exists_rotate_strictlyPositivePrefixes l h htie
  · rintro ⟨r, hr, hgood⟩
    have h := hgood l.length (by omega) (by simp)
    have htake : (l.rotate r).take l.length = l.rotate r := by
      apply List.take_of_length_le
      simp
    rw [htake] at h
    simpa only [(List.rotate_perm l r).sum_eq] using h

end CollatzMoonshot
