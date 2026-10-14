/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Counting periodic sets of integers

A predicate `P` on `ℤ` with period `Q` is described by its residue count
`resCount Q P = #{0 ≤ r < Q : P r}`.  The density estimates for the transient-cone cores of `κ`
and `σ_τ` only use four operations on such predicates, each with a residue-count bound:

* `IsPer.pull`, `resCount_pull_le`: the predicate `y ≡ r (mod m) ∧ P (a ⌊y/m⌋ + b)` has period
  `mQ` and at most as many residues as `P` when `a` is a unit mod `Q`;
* `IsPer.or`, `resCount_or_le`: unions;
* `IsPer.mul`, `resCount_mul_le`: refining the period;
* `box_count_le`: at most `resCount Q P · (2⌊X/Q⌋ + 2)` points of `[-X, X]` satisfy `P`.
-/

namespace CollatzMoonshot.Amusical.AntiKohlPeriodic

/-- `P` has period `Q`. -/
def IsPer (Q : ℕ) (P : ℤ → Prop) : Prop :=
  ∀ x : ℤ, P (x + Q) ↔ P x

open Classical in
/-- The number of residues `0 ≤ r < Q` satisfying `P`. -/
noncomputable def resCount (Q : ℕ) (P : ℤ → Prop) : ℕ :=
  ((Finset.Ico (0 : ℤ) Q).filter P).card

variable {Q : ℕ} {P P₁ P₂ : ℤ → Prop}

theorem IsPer.add_mul (h : IsPer Q P) (x k : ℤ) : P (x + Q * k) ↔ P x := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
      rw [show x + (Q : ℤ) * ((k : ℤ) + 1) = (x + Q * k) + Q by ring, h, ih]
  | pred k ih =>
      have hk := h (x + Q * (-(k : ℤ) - 1))
      rw [show x + (Q : ℤ) * (-(k : ℤ) - 1) + Q = x + Q * (-(k : ℤ)) by ring] at hk
      exact hk.symm.trans ih

theorem IsPer.emod (h : IsPer Q P) (x : ℤ) : P x ↔ P (x % Q) := by
  have hx := h.add_mul (x % Q) (x / Q)
  rw [Int.emod_add_mul_ediv] at hx
  exact hx

theorem IsPer.or (h₁ : IsPer Q P₁) (h₂ : IsPer Q P₂) : IsPer Q (fun x => P₁ x ∨ P₂ x) :=
  fun x => or_congr (h₁ x) (h₂ x)

theorem IsPer.mul (h : IsPer Q P) (k : ℕ) : IsPer (k * Q) P := by
  intro x
  have hx := h.add_mul x k
  push_cast
  rw [show x + (k : ℤ) * Q = x + Q * k by ring]
  exact hx

theorem IsPer.pull (h : IsPer Q P) {m : ℕ} (hm : 0 < m) (r a b : ℤ) :
    IsPer (m * Q) (fun y => y % m = r ∧ P (a * (y / m) + b)) := by
  intro y
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have h1 : (y + ((m * Q : ℕ) : ℤ)) % m = y % m := by
    push_cast
    exact Int.add_mul_emod_self_left y m Q
  have h2 : (y + ((m * Q : ℕ) : ℤ)) / m = y / m + Q := by
    push_cast
    exact Int.add_mul_ediv_left y Q hm'
  simp only [h1, h2]
  rw [show a * (y / m + Q) + b = (a * (y / m) + b) + Q * a by ring, h.add_mul]

theorem resCount_mono (hPP : ∀ x, P₁ x → P₂ x) : resCount Q P₁ ≤ resCount Q P₂ := by
  classical
  unfold resCount
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter] at hy ⊢
  exact ⟨hy.1, hPP y hy.2⟩

theorem resCount_or_le :
    resCount Q (fun x => P₁ x ∨ P₂ x) ≤ resCount Q P₁ + resCount Q P₂ := by
  classical
  unfold resCount
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_union] at hy ⊢
  tauto

theorem resCount_pull_le (hQ : 0 < Q) (h : IsPer Q P) {m : ℕ} (hm : 0 < m) (r a b : ℤ)
    (ha : IsCoprime a (Q : ℤ)) :
    resCount (m * Q) (fun y => y % m = r ∧ P (a * (y / m) + b)) ≤ resCount Q P := by
  classical
  unfold resCount
  have hQz : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  apply Finset.card_le_card_of_injOn (fun y => (a * (y / m) + b) % Q)
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico] at hy ⊢
    refine ⟨⟨Int.emod_nonneg _ hQz.ne', Int.emod_lt_of_pos _ hQz⟩, ?_⟩
    exact (h.emod _).mp hy.2.2
  · intro y hy y' hy' heq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico] at hy hy' heq
    have hlt : ∀ z : ℤ, 0 ≤ z → z < ((m * Q : ℕ) : ℤ) → 0 ≤ z / m ∧ z / m < Q := by
      intro z hz0 hz
      refine ⟨Int.ediv_nonneg hz0 hmz.le, Int.ediv_lt_of_lt_mul hmz ?_⟩
      push_cast at hz
      linarith
    obtain ⟨hy0, hyQ⟩ := hlt y hy.1.1 hy.1.2
    obtain ⟨hy0', hyQ'⟩ := hlt y' hy'.1.1 hy'.1.2
    have hmod : a * (y / m) + b ≡ a * (y' / m) + b [ZMOD Q] := heq
    have hmod' : a * (y / m) ≡ a * (y' / m) [ZMOD Q] := Int.ModEq.add_right_cancel' b hmod
    have hdvd : (Q : ℤ) ∣ a * (y' / m - y / m) := by
      have := hmod'.dvd
      rwa [← mul_sub] at this
    have hdvd' : (Q : ℤ) ∣ y' / m - y / m := (ha.symm.dvd_of_dvd_mul_left hdvd)
    have hq : y / m = y' / m := by
      obtain ⟨t, ht⟩ := hdvd'
      have ht0 : t = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hneg | hpos
        · have : (Q : ℤ) * t ≤ -Q := by nlinarith
          linarith
        · have : (Q : ℤ) ≤ Q * t := by nlinarith
          linarith
      subst ht0
      linarith
    have e1 := Int.mul_ediv_add_emod y m
    have e2 := Int.mul_ediv_add_emod y' m
    rw [hq, hy.2.1] at e1
    rw [hy'.2.1] at e2
    linarith

theorem resCount_mul_le (hQ : 0 < Q) (h : IsPer Q P) (k : ℕ) :
    resCount (k * Q) P ≤ k * resCount Q P := by
  classical
  unfold resCount
  have hQz : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hcard : ((Finset.Ico (0 : ℤ) k) ×ˢ ((Finset.Ico (0 : ℤ) Q).filter P)).card =
      k * ((Finset.Ico (0 : ℤ) Q).filter P).card := by
    rw [Finset.card_product, Int.card_Ico]
    simp
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun y : ℤ => (y / (Q : ℤ), y % (Q : ℤ)))
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico, Finset.coe_product,
      Set.mem_prod, Finset.mem_coe] at hy ⊢
    refine ⟨⟨Int.ediv_nonneg hy.1.1 hQz.le, Int.ediv_lt_of_lt_mul hQz ?_⟩,
      ⟨Int.emod_nonneg _ hQz.ne', Int.emod_lt_of_pos _ hQz⟩, (h.emod _).mp hy.2⟩
    have := hy.1.2
    push_cast at this
    linarith
  · intro y _ y' _ heq
    simp only [Prod.mk.injEq] at heq
    have e1 := Int.mul_ediv_add_emod y Q
    have e2 := Int.mul_ediv_add_emod y' Q
    rw [heq.1, heq.2] at e1
    linarith

open Classical in
theorem box_count_le (hQ : 0 < Q) (h : IsPer Q P) (X : ℕ) :
    ((Finset.Icc (-(X : ℤ)) X).filter P).card ≤ resCount Q P * (2 * (X / Q) + 2) := by
  classical
  unfold resCount
  have hQz : (0 : ℤ) < Q := by exact_mod_cast hQ
  set q : ℤ := ((X / Q : ℕ) : ℤ) with hqdef
  have hqX : q = (X : ℤ) / Q := by rw [hqdef, Int.natCast_div]
  have hcard : (((Finset.Ico (0 : ℤ) Q).filter P) ×ˢ (Finset.Icc (-q - 1) q)).card =
      ((Finset.Ico (0 : ℤ) Q).filter P).card * (2 * (X / Q) + 2) := by
    rw [Finset.card_product, Int.card_Icc]
    congr 1
    omega
  rw [← hcard]
  convert Finset.card_le_card_of_injOn (fun y : ℤ => (y % (Q : ℤ), y / (Q : ℤ))) ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc, Finset.coe_product,
      Set.mem_prod, Finset.mem_coe, Finset.mem_Ico] at hy ⊢
    refine ⟨⟨⟨Int.emod_nonneg _ hQz.ne', Int.emod_lt_of_pos _ hQz⟩, (h.emod _).mp hy.2⟩, ?_, ?_⟩
    · rw [Int.le_ediv_iff_mul_le hQz]
      have e := Int.mul_ediv_add_emod (X : ℤ) Q
      have hlt := Int.emod_lt_of_pos (X : ℤ) hQz
      rw [← hqX] at e
      nlinarith [hy.1.1]
    · rw [hqX]
      exact Int.ediv_le_ediv hQz hy.1.2
  · intro y _ y' _ heq
    simp only [Prod.mk.injEq] at heq
    have e1 := Int.mul_ediv_add_emod y Q
    have e2 := Int.mul_ediv_add_emod y' Q
    rw [heq.1, heq.2] at e1
    linarith

end CollatzMoonshot.Amusical.AntiKohlPeriodic
