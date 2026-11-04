/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawProb

/-!
# The orbit word law: Terras with constraints

`cardMatchSet_holds` proves `CardMatchSet`: among `r < 2^m`, prescribing the letters at any set
`S` of positions below `m` leaves `2^(m − |S|)` residues.  Adding `2^m` leaves the letters below
`m` alone and flips letter `m` (Terras), so each step of the induction either halves (`m ∈ S`) or
doubles nothing away (`m ∉ S`).  One and two windows (`cardMatchOne_holds`,
`cardMatchTwo_holds`) are the cases `S = [i, i + |u|)` and its union with `[i', i' + |u|)`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-- Letter `j` does not see adding `2^k` when `j < k`. -/
theorem accWord_two_pow_add_of_lt {j k : ℕ} (h : j < k) (r : ℕ) :
    accWord (2 ^ k + r) j = accWord r j := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [add_comm, show 2 ^ (j + c + 1) = 2 ^ c * 2 ^ (j + 1) by ring]
  exact accWord_add_mul_two_pow_succ r _ j

/-- A constraint set splits off its top position. -/
theorem forall_mem_iff_erase (P : ℕ → Prop) (S : Finset ℕ) (m : ℕ) :
    (∀ s ∈ S, P s) ↔ (∀ s ∈ S.erase m, P s) ∧ (m ∈ S → P m) := by
  constructor
  · exact fun h => ⟨fun s hs => h s (Finset.mem_of_mem_erase hs), h m⟩
  · rintro ⟨h1, h2⟩ s hs
    by_cases hsm : s = m
    · exact hsm ▸ h2 (hsm ▸ hs)
    · exact h1 s (Finset.mem_erase.mpr ⟨hsm, hs⟩)

/-- **Terras with constraints** (`CardMatchSet`). -/
theorem cardMatchSet_holds : CardMatchSet := by
  intro g S m
  induction m generalizing S with
  | zero =>
    intro hS
    have hS0 : S = ∅ := Finset.eq_empty_of_forall_notMem fun s hs => by
      have := hS s hs
      omega
    subst hS0
    simp
  | succ m ih =>
    intro hS
    set S' := S.erase m with hS'def
    have hS' : ∀ s ∈ S', s < m := by
      intro s hs
      have := hS s (Finset.mem_of_mem_erase hs)
      have := Finset.ne_of_mem_erase hs
      omega
    have hcount := ih S' hS'
    rw [Finset.card_filter] at hcount ⊢
    rw [pow_succ, mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
    have hpt : ∀ r ∈ Finset.range (2 ^ m),
        ((if ∀ s ∈ S, accWord r s = g s then 1 else 0) +
          (if ∀ s ∈ S, accWord (2 ^ m + r) s = g s then 1 else 0) : ℕ) =
        (if m ∈ S then 1 else 2) * (if ∀ s ∈ S', accWord r s = g s then 1 else 0) := by
      intro r _
      have hlow : (∀ s ∈ S', accWord (2 ^ m + r) s = g s) ↔ ∀ s ∈ S', accWord r s = g s :=
        forall₂_congr fun s hs => by rw [accWord_two_pow_add_of_lt (hS' s hs)]
      have htop : accWord (2 ^ m + r) m = !(accWord r m) := by
        rw [add_comm]; exact accWord_add_two_pow r m
      have e1 := forall_mem_iff_erase (fun s => accWord r s = g s) S m
      have e2 := forall_mem_iff_erase (fun s => accWord (2 ^ m + r) s = g s) S m
      rw [hlow, htop] at e2
      rw [← hS'def] at e1
      simp only [e1, e2]
      by_cases hm : m ∈ S <;> by_cases hP : ∀ s ∈ S', accWord r s = g s
      all_goals first
        | have hP' : (∀ s ∈ S', accWord r s = g s) = True := eq_true hP
          simp only [hP']
        | have hP' : (∀ s ∈ S', accWord r s = g s) = False := eq_false hP
          simp only [hP']
      all_goals cases accWord r m <;> cases g m <;> simp [hm]
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, hcount]
    by_cases hm : m ∈ S
    · have hc : S'.card = S.card - 1 := Finset.card_erase_of_mem hm
      have hc1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨m, hm⟩
      rw [if_pos hm, one_mul, hc]
      congr 1
      omega
    · have hSS : S' = S := Finset.erase_eq_of_notMem hm
      have hle : S.card ≤ m := by
        rw [hSS] at hS'
        have : S ⊆ Finset.range m := fun s hs => Finset.mem_range.mpr (hS' s hs)
        simpa using Finset.card_le_card this
      rw [if_neg hm, hSS, show m + 1 - S.card = (m - S.card) + 1 by omega, pow_succ]
      ring

/-- The letters of a window at `i`, as a function of the position. -/
def winLetters (u : List Bool) (i : ℕ) : ℕ → Bool := fun s => u.getD (s - i) false

/-- A window is a constraint on the positions `[i, i + |u|)`. -/
theorem windowMatch_iff_forall (u : List Bool) (i r : ℕ) :
    WindowMatch (fun s => u.getD s false) u.length i r ↔
      ∀ s ∈ Finset.Ico i (i + u.length), accWord r s = winLetters u i s := by
  constructor
  · intro h s hs
    rw [Finset.mem_Ico] at hs
    have := h (s - i) (by omega)
    rwa [show i + (s - i) = s by omega] at this
  · intro h s hs
    have := h (i + s) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    rw [this, winLetters, Nat.add_sub_cancel_left]

/-- **One window** (`CardMatchOne`). -/
theorem cardMatchOne_holds : CardMatchOne := by
  intro u m i him
  have := cardMatchSet_holds (winLetters u i) (Finset.Ico i (i + u.length)) m
    (fun s hs => by rw [Finset.mem_Ico] at hs; omega)
  rw [Nat.card_Ico, Nat.add_sub_cancel_left] at this
  rw [← this]
  congr 1
  exact Finset.filter_congr fun r _ => windowMatch_iff_forall u i r

/-- **Two disjoint windows** (`CardMatchTwo`). -/
theorem cardMatchTwo_holds : CardMatchTwo := by
  intro u m i i' hii' him
  set g : ℕ → Bool := fun s => if s < i' then winLetters u i s else winLetters u i' s with hg
  have hdisj : Disjoint (Finset.Ico i (i + u.length)) (Finset.Ico i' (i' + u.length)) :=
    Finset.disjoint_left.mpr fun s h1 h2 => by
      rw [Finset.mem_Ico] at h1 h2
      omega
  have := cardMatchSet_holds g (Finset.Ico i (i + u.length) ∪ Finset.Ico i' (i' + u.length)) m
    (fun s hs => by
      rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico] at hs
      omega)
  rw [Finset.card_union_of_disjoint hdisj, Nat.card_Ico, Nat.card_Ico, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel_left, ← two_mul] at this
  rw [← this]
  congr 1
  refine Finset.filter_congr fun r _ => ?_
  rw [windowMatch_iff_forall, windowMatch_iff_forall]
  constructor
  · rintro ⟨h1, h2⟩ s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · have hs' := Finset.mem_Ico.mp hs
      rw [h1 s hs, hg]
      simp only
      rw [if_pos (by omega)]
    · have hs' := Finset.mem_Ico.mp hs
      rw [h2 s hs, hg]
      simp only
      rw [if_neg (by omega)]
  · intro h
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · have hs' := Finset.mem_Ico.mp hs
      rw [h s (Finset.mem_union_left _ hs), hg]
      simp only
      rw [if_pos (by omega)]
    · have hs' := Finset.mem_Ico.mp hs
      rw [h s (Finset.mem_union_right _ hs), hg]
      simp only
      rw [if_neg (by omega)]

end CollatzMoonshot.Conjugacy
