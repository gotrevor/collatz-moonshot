/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Stopped prefixes (helpers for NB and the pattern count)

`runs`, `upTo` and `SP` are verbatim copies of `trueRuns`, `boolListsUpTo` and `stoppedPrefixes`
(the main file identifies them).  A stopped prefix with `τ + 1 ≥ 2` `E`'s is `E :: s'` with
`s' ∈ SP τ k M`, or `E :: O^{c+1} ++ s'` with `s' ∈ SP τ (k − 1) (M − c − 1)`; both bounds follow by
induction on `τ` and Pascal's rule (the `O`-gaps sum geometrically for NB, by the hockey stick for
the count).
-/

namespace CollatzMoonshot.Amusical.NearCycleEntropy

open Finset List

/-- A copy of `trueRuns`. -/
def runs : List Bool → ℕ
  | [] => 0
  | b :: s => runs s + if b = true ∧ s.head? ≠ some true then 1 else 0

/-- A copy of `boolListsUpTo`. -/
def upTo : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => insert [] ((upTo n).biUnion fun s => {true :: s, false :: s})

/-- A copy of `stoppedPrefixes`. -/
def SP (τ k M : ℕ) : Finset (List Bool) :=
  (upTo (τ + M)).filter fun s =>
    s.head? = some true ∧ s.getLast? = some true ∧ s.count true = τ ∧ s.count false ≤ M ∧
      runs s ≤ k

theorem mem_upTo (n : ℕ) (s : List Bool) : s ∈ upTo n ↔ s.length ≤ n := by
  induction n generalizing s with
  | zero => cases s <;> simp [upTo]
  | succ n ih =>
    cases s with
    | nil => simp [upTo]
    | cons b s =>
      simp only [upTo, Finset.mem_insert, reduceCtorEq, false_or, Finset.mem_biUnion,
        Finset.mem_insert, Finset.mem_singleton, List.cons.injEq, length_cons]
      constructor
      · rintro ⟨t, ht, h | h⟩ <;> · obtain ⟨-, rfl⟩ := h; have := (ih _).mp ht; omega
      · intro h
        refine ⟨s, (ih s).mpr (by omega), ?_⟩
        cases b <;> simp

theorem mem_SP {τ k M : ℕ} {s : List Bool} : s ∈ SP τ k M ↔
    s.head? = some true ∧ s.getLast? = some true ∧ s.count true = τ ∧ s.count false ≤ M ∧
      runs s ≤ k := by
  rw [SP, Finset.mem_filter, mem_upTo]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [← count_true_add_count_false]
    omega

theorem runs_replicate_false (c : ℕ) (s : List Bool) :
    runs (replicate c false ++ s) = runs s := by
  induction c with
  | zero => rfl
  | succ c ih => simp [replicate_succ, runs, ih]

theorem runs_cons_true_of_head {s : List Bool} (h : s.head? = some true) :
    runs (true :: s) = runs s := by
  simp [runs, h]

theorem runs_true_false (c : ℕ) (s : List Bool) :
    runs (true :: (replicate (c + 1) false ++ s)) = runs s + 1 := by
  rw [runs, runs_replicate_false]
  simp [replicate_succ]

/-- Peel the leading `O`'s of a list containing an `E`. -/
theorem exists_replicate_false {r : List Bool} (h : true ∈ r) :
    ∃ c s, r = replicate c false ++ s ∧ s.head? = some true := by
  induction r with
  | nil => simp at h
  | cons b r ih =>
    cases b with
    | true => exact ⟨0, true :: r, by simp, rfl⟩
    | false =>
      obtain ⟨c, s, rfl, hs⟩ := ih (by simpa using h)
      exact ⟨c + 1, s, by simp [replicate_succ], hs⟩

/-- **The decomposition.** -/
theorem SP_succ_subset (τ k M : ℕ) (hτ : 1 ≤ τ) :
    SP (τ + 1) k M ⊆ (SP τ k M).image (true :: ·) ∪
      (Finset.range M).biUnion fun c =>
        (SP τ (k - 1) (M - 1 - c)).image fun s => true :: (replicate (c + 1) false ++ s) := by
  intro s hs
  obtain ⟨hh, hl, ht, hf, hr⟩ := mem_SP.mp hs
  obtain ⟨r, rfl⟩ : ∃ r, s = true :: r := by
    cases s with
    | nil => simp at hh
    | cons b r => simp at hh; exact ⟨r, by rw [hh]⟩
  have hrt : true ∈ r := by
    rw [count_cons_self] at ht
    exact count_pos_iff.mp (by omega)
  obtain ⟨c, s', rfl, hs'⟩ := exists_replicate_false hrt
  have hne : s' ≠ [] := by rintro rfl; simp at hs'
  have hl' : s'.getLast? = some true := by
    rw [← cons_append, getLast?_append_of_ne_nil _ hne] at hl; exact hl
  have ht' : s'.count true = τ := by
    simp [count_replicate] at ht; omega
  have hf' : s'.count false + c ≤ M := by
    simp at hf; omega
  rw [Finset.mem_union]
  rcases c with _ | c
  · left
    rw [Finset.mem_image]
    refine ⟨s', mem_SP.mpr ⟨hs', hl', ht', by omega, ?_⟩, by simp⟩
    rwa [replicate_zero, nil_append, runs_cons_true_of_head hs'] at hr
  · right
    rw [Finset.mem_biUnion]
    refine ⟨c, Finset.mem_range.mpr (by omega), Finset.mem_image.mpr ⟨s', mem_SP.mpr
      ⟨hs', hl', ht', by omega, ?_⟩, rfl⟩⟩
    rw [runs_true_false] at hr; omega

theorem SP_one_subset (k M : ℕ) : SP 1 k M ⊆ if 1 ≤ k then {[true]} else ∅ := by
  intro s hs
  obtain ⟨hh, hl, ht, -, hr⟩ := mem_SP.mp hs
  obtain ⟨r, rfl⟩ : ∃ r, s = true :: r := by
    cases s with
    | nil => simp at hh
    | cons b r => simp at hh; exact ⟨r, by rw [hh]⟩
  have hr0 : r = [] := by
    by_contra hne
    rw [count_cons_self] at ht
    have : r.getLast? = some true := by
      rw [← singleton_append, getLast?_append_of_ne_nil _ hne] at hl; exact hl
    have := mem_of_getLast? this
    have := count_pos_iff.mpr this
    omega
  subst hr0
  have : runs [true] = 1 := rfl
  split_ifs with hk
  · simp
  · omega

/-- Pascal's rule under a weighted partial row sum. -/
theorem sum_choose_succ {R : Type*} [CommSemiring R] (t k : ℕ) (a : ℕ → R) :
    ∑ i ∈ Finset.range (k + 1), ((t + 1).choose i : R) * a i =
      ∑ i ∈ Finset.range (k + 1), (t.choose i : R) * a i +
        ∑ i ∈ Finset.range k, (t.choose i : R) * a (i + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun i => (t.choose i : R) * a i)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  ring

/-- The hockey stick, reflected. -/
theorem sum_range_choose_reflect (M i : ℕ) :
    ∑ c ∈ Finset.range M, (M - 1 - c).choose i = M.choose (i + 1) := by
  rw [Finset.sum_range_reflect (fun c => c.choose i) M]
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ', add_comm]

theorem sum_biUnion_le_of_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ℕ)
    (t : ℕ → Finset ι) (f : ι → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ c ∈ s, ∑ x ∈ t c, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have h0 : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg fun x _ => hf x
    linarith

/-- **The pattern count.** -/
theorem card_SP_le (t k M : ℕ) :
    (SP (t + 1) k M).card ≤
      ∑ i ∈ Finset.range k, t.choose i * M.choose i := by
  induction t generalizing k M with
  | zero =>
    refine (Finset.card_le_card (SP_one_subset k M)).trans ?_
    rcases k with _ | k
    · simp
    · rw [if_pos (by omega), Finset.sum_range_succ']; simp
  | succ t ih =>
    refine (Finset.card_le_card (SP_succ_subset (t + 1) k M (by omega))).trans ?_
    refine (Finset.card_union_le _ _).trans ?_
    refine (add_le_add Finset.card_image_le (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun c _ => Finset.card_image_le))).trans ?_
    refine (add_le_add (ih k M) (Finset.sum_le_sum fun c _ => ih (k - 1) (M - 1 - c))).trans ?_
    rcases k with _ | k
    · simp
    · rw [Nat.add_sub_cancel, Finset.sum_comm]
      have h := sum_choose_succ (R := ℕ) t k (fun i => M.choose i)
      simp only [Nat.cast_id] at h
      rw [h]
      gcongr with i
      rw [← Finset.mul_sum, sum_range_choose_reflect]

/-- **NB.** -/
theorem sum_SP_le (t k M : ℕ) :
    ∑ s ∈ SP (t + 1) k M, ((1 : ℝ) / 2) ^ s.length ≤
      ∑ j ∈ Finset.range k, (t.choose j : ℝ) / 2 ^ (t + 1) := by
  induction t generalizing k M with
  | zero =>
    refine (Finset.sum_le_sum_of_subset_of_nonneg (SP_one_subset k M)
      (fun _ _ _ => by positivity)).trans ?_
    rcases k with _ | k
    · simp
    · rw [if_pos (by omega), Finset.sum_range_succ']
      simp only [Finset.sum_singleton, length_singleton, pow_one, Nat.choose_zero_right]
      have : ∀ i ∈ Finset.range k, ((Nat.choose 0 (i + 1) : ℕ) : ℝ) / 2 ^ (0 + 1) = 0 := by
        intro i _; simp
      rw [Finset.sum_eq_zero this]; norm_num
  | succ t ih =>
    have hw : ∀ k', 0 ≤ ∑ j ∈ Finset.range k', (t.choose j : ℝ) / 2 ^ (t + 1) :=
      fun k' => Finset.sum_nonneg fun _ _ => by positivity
    refine (Finset.sum_le_sum_of_subset_of_nonneg (SP_succ_subset (t + 1) k M (by omega))
      (fun _ _ _ => by positivity)).trans ?_
    have hU := Finset.sum_union_inter (f := fun s : List Bool => ((1 : ℝ) / 2) ^ s.length)
      (s₁ := (SP (t + 1) k M).image (true :: ·))
      (s₂ := (Finset.range M).biUnion fun c =>
        (SP (t + 1) (k - 1) (M - 1 - c)).image fun s => true :: (replicate (c + 1) false ++ s))
    have h0 : (0 : ℝ) ≤ ∑ s ∈ (SP (t + 1) k M).image (true :: ·) ∩
        (Finset.range M).biUnion (fun c => (SP (t + 1) (k - 1) (M - 1 - c)).image
          fun s => true :: (replicate (c + 1) false ++ s)), ((1 : ℝ) / 2) ^ s.length :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hA : ∑ s ∈ (SP (t + 1) k M).image (true :: ·), ((1 : ℝ) / 2) ^ s.length =
        1 / 2 * ∑ s ∈ SP (t + 1) k M, ((1 : ℝ) / 2) ^ s.length := by
      rw [Finset.sum_image (fun _ _ _ _ h => List.cons_injective h), Finset.mul_sum]
      simp [pow_succ, mul_comm]
    have hB := sum_biUnion_le_of_nonneg (Finset.range M)
      (fun c => (SP (t + 1) (k - 1) (M - 1 - c)).image
        fun s => true :: (replicate (c + 1) false ++ s))
      (fun s : List Bool => ((1 : ℝ) / 2) ^ s.length) (fun _ => by positivity)
    have hB' : ∀ c ∈ Finset.range M, ∑ s ∈ (SP (t + 1) (k - 1) (M - 1 - c)).image
          (fun s => true :: (replicate (c + 1) false ++ s)), ((1 : ℝ) / 2) ^ s.length ≤
        ((1 : ℝ) / 2) ^ (c + 2) *
          ∑ j ∈ Finset.range (k - 1), (t.choose j : ℝ) / 2 ^ (t + 1) := by
      intro c _
      rw [Finset.sum_image (fun _ _ _ _ h => List.append_cancel_left (List.cons_injective h))]
      calc _ = ((1 : ℝ) / 2) ^ (c + 2) * ∑ s ∈ SP (t + 1) (k - 1) (M - 1 - c),
            ((1 : ℝ) / 2) ^ s.length := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            simp only [length_cons, length_append, length_replicate]
            rw [← pow_add]; congr 1; omega
        _ ≤ _ := mul_le_mul_of_nonneg_left (ih _ _) (by positivity)
    have hgeo : ∑ c ∈ Finset.range M, ((1 : ℝ) / 2) ^ (c + 2) ≤ 1 / 2 := by
      have := sum_geometric_two_le M
      have he : ∑ c ∈ Finset.range M, ((1 : ℝ) / 2) ^ (c + 2) =
          1 / 4 * ∑ c ∈ Finset.range M, ((1 : ℝ) / 2) ^ c := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => ?_; ring
      rw [he]; linarith
    have hB'' := (hB.trans (Finset.sum_le_sum hB')).trans_eq (Finset.sum_mul ..).symm
    have hB3 : (∑ c ∈ Finset.range M, ((1 : ℝ) / 2) ^ (c + 2)) *
        ∑ j ∈ Finset.range (k - 1), (t.choose j : ℝ) / 2 ^ (t + 1) ≤
        1 / 2 * ∑ j ∈ Finset.range (k - 1), (t.choose j : ℝ) / 2 ^ (t + 1) :=
      mul_le_mul_of_nonneg_right hgeo (hw _)
    have hI := ih k M
    have key : 1 / 2 * ∑ j ∈ Finset.range k, (t.choose j : ℝ) / 2 ^ (t + 1) +
        1 / 2 * ∑ j ∈ Finset.range (k - 1), (t.choose j : ℝ) / 2 ^ (t + 1) ≤
        ∑ j ∈ Finset.range k, ((t + 1).choose j : ℝ) / 2 ^ (t + 1 + 1) := by
      rcases k with _ | k
      · simp
      · rw [Nat.add_sub_cancel]
        have h := sum_choose_succ (R := ℝ) t k (fun _ => 1 / 2 ^ (t + 1 + 1))
        simp only [div_eq_mul_one_div ((Nat.choose _ _ : ℕ) : ℝ)]
        rw [h, Finset.mul_sum, Finset.mul_sum]
        apply le_of_eq
        congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> rw [pow_succ] <;> ring
    linarith

theorem SP_zero (k M : ℕ) : SP 0 k M = ∅ := by
  ext s
  simp only [Finset.notMem_empty, iff_false]
  intro hs
  obtain ⟨hh, -, ht, -⟩ := mem_SP.mp hs
  have := count_pos_iff.mpr (mem_of_mem_head? hh)
  omega

end CollatzMoonshot.Amusical.NearCycleEntropy
