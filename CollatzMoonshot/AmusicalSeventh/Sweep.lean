/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalSeventh.Sparse

/-!
# Assembling the sparse sweep

The deterministic half of `sparse_sweep`: every visit of an infinite orbit below `X` within
time `T` is either an exceptional center (a strict descent at some time `K < i ≤ L`) or lies
within `K` steps of an `(L-K)`-window minimum, and those minima are packed apart along the
orbit.
-/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- Every power of `U` preserves the nonnegative integers. -/
theorem amusicalPerm_zpow_nonneg {z : ℤ} (hz : 0 ≤ z) (t : ℤ) : 0 ≤ (amusicalPerm ^ t) z := by
  have hf : ∀ k : ℕ, 0 ≤ amusical^[k] z := by
    intro k
    induction k with
    | zero => simpa using hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact amusical_nonneg ih
  have hb : ∀ k : ℕ, 0 ≤ amusicalInv^[k] z := by
    intro k
    induction k with
    | zero => simpa using hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact amusicalInv_nonneg ih
  rcases Int.eq_nat_or_neg t with ⟨k, rfl | rfl⟩
  · rw [← amusical_iterate_eq_perm_pow]; exact hf k
  · rw [← amusicalInv_iterate_eq_perm_pow]; exact hb k

/-- **Deterministic sweep count.**  The visits of an infinite orbit below `X` at times
`|j| ≤ T`, weighted by the packing length `L-K+1`, are bounded by the exceptional descent
centers plus `(2K+1)` copies of the packing bound for `(L-K)`-window minima. -/
theorem sweep_card_mul_le (K L T X : ℕ) (hKL : K ≤ L) (x : ℤ)
    (hinf : (amusicalOrbit x).Infinite) :
    (L - K + 1) * ((Finset.Icc (-(T : ℤ)) T).filter
        fun j => 0 ≤ (amusicalPerm ^ j) x ∧ (amusicalPerm ^ j) x < X).card ≤
      (L - K + 1) * Nat.count (fun n : ℕ => ∃ i : ↥(Finset.Icc (K + 1) L),
        (amusical^[i] (n : ℤ) < n ∨ amusicalInv^[i] (n : ℤ) < n)) X +
      (2 * K + 1) * (2 * (T + L) + 1) := by
  classical
  set F := (Finset.Icc (-(T : ℤ)) T).filter
    fun j => 0 ≤ (amusicalPerm ^ j) x ∧ (amusicalPerm ^ j) x < X with hF
  set E : ℕ → Prop := fun n : ℕ => ∃ i : ↥(Finset.Icc (K + 1) L),
    (amusical^[i] (n : ℤ) < n ∨ amusicalInv^[i] (n : ℤ) < n) with hE
  have hinj := perm_zpow_apply_injective_of_infinite amusicalPerm hinf
  have hmemF : ∀ j ∈ F, |j| ≤ (T : ℤ) ∧ 0 ≤ (amusicalPerm ^ j) x ∧
      (amusicalPerm ^ j) x < X := by
    intro j hj
    rw [hF, Finset.mem_filter, Finset.mem_Icc] at hj
    exact ⟨abs_le.mpr hj.1, hj.2⟩
  -- exceptional visits
  set H := F.filter fun j => E ((amusicalPerm ^ j) x).toNat with hH
  set G := F.filter fun j => ¬ E ((amusicalPerm ^ j) x).toNat with hG
  have hsplit : H.card + G.card = F.card := by
    rw [hH, hG]; exact Finset.card_filter_add_card_filter_not _
  have hHcard : H.card ≤ Nat.count E X := by
    rw [Nat.count_eq_card_filter_range]
    apply Finset.card_le_card_of_injOn (fun j => ((amusicalPerm ^ j) x).toNat)
    · intro j hj
      have hj' := Finset.mem_filter.mp hj
      obtain ⟨-, h0, hX⟩ := hmemF j hj'.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hj'.2⟩
      show ((amusicalPerm ^ j) x).toNat < X
      omega
    · intro a ha b hb hab
      have ha' := hmemF a (Finset.mem_filter.mp ha).1
      have hb' := hmemF b (Finset.mem_filter.mp hb).1
      apply hinj
      dsimp only at hab ⊢
      omega
  -- nonexceptional visits sit near packed window minima
  choose tm htm hmin using fun n : ℤ => exists_centered_window_minimizer L n
  set M := (Finset.range X).filter fun m : ℕ => IsWindowMin (L - K) (m : ℤ) ∧
    ∃ j : ℤ, (amusicalPerm ^ j) x = m ∧ |j| ≤ ((T + K : ℕ) : ℤ) with hM
  have hnear : ∀ j ∈ G, |tm ((amusicalPerm ^ j) x)| ≤ K := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    obtain ⟨-, h0, -⟩ := hmemF j hj'.1
    set n := (amusicalPerm ^ j) x with hn
    by_contra hout
    push Not at hout
    have hinfn : (amusicalOrbit n).Infinite := by
      rwa [amusicalOrbit_eq_of_mem ⟨j, rfl⟩]
    apply hj'.2
    have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg h0
    rcases centered_minimizer_outside_implies_descent hinfn (htm n) hout (hmin n) with
      ⟨i, hKi, hiL, hi⟩ | ⟨i, hKi, hiL, hi⟩
    · exact ⟨⟨i, Finset.mem_Icc.mpr ⟨hKi, hiL⟩⟩, Or.inl (by rw [hcast]; exact hi)⟩
    · exact ⟨⟨i, Finset.mem_Icc.mpr ⟨hKi, hiL⟩⟩, Or.inr (by rw [hcast]; exact hi)⟩
  have hGcard : G.card ≤ M.card * (2 * K + 1) := by
    have hprod : (M ×ˢ Finset.Icc (-(K : ℤ)) K).card = M.card * (2 * K + 1) := by
      rw [Finset.card_product, Int.card_Icc]
      congr 1
      omega
    rw [← hprod]
    apply Finset.card_le_card_of_injOn (fun j =>
      (((amusicalPerm ^ (tm ((amusicalPerm ^ j) x) + j)) x).toNat, tm ((amusicalPerm ^ j) x)))
    · intro j hj
      have hj' := Finset.mem_filter.mp hj
      obtain ⟨hjT, h0, hX⟩ := hmemF j hj'.1
      have ht := hnear j hj
      set n := (amusicalPerm ^ j) x with hn
      set t := tm n with ht_def
      have hval : (amusicalPerm ^ (t + j)) x = (amusicalPerm ^ t) n := by
        rw [zpow_add, Equiv.Perm.mul_apply]
      have hle : (amusicalPerm ^ t) n ≤ n := by simpa using hmin n 0 (by simp)
      have hnn : 0 ≤ (amusicalPerm ^ t) n := amusicalPerm_zpow_nonneg h0 t
      have hwin : IsWindowMin (L - K) ((amusicalPerm ^ t) n) :=
        isWindowMin_sub_of_centered_minimizer hKL ht (hmin n)
      have hcast : ((((amusicalPerm ^ t) n).toNat : ℕ) : ℤ) = (amusicalPerm ^ t) n :=
        Int.toNat_of_nonneg hnn
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · dsimp only
        rw [hval]
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, t + j, ?_, ?_⟩
        · rw [hcast]; exact hwin
        · rw [hcast, hval]
        · have h1 := abs_add_le t j
          push_cast
          omega
      · dsimp only
        exact Finset.mem_Icc.mpr (abs_le.mp ht)
    · intro a ha b hb hab
      have ha' := hmemF a (Finset.mem_filter.mp ha).1
      have hb' := hmemF b (Finset.mem_filter.mp hb).1
      simp only [Prod.mk.injEq] at hab
      obtain ⟨hv, htt⟩ := hab
      have hna := amusicalPerm_zpow_nonneg ha'.2.1 (tm ((amusicalPerm ^ a) x))
      have hnb := amusicalPerm_zpow_nonneg hb'.2.1 (tm ((amusicalPerm ^ b) x))
      rw [← Equiv.Perm.mul_apply, ← zpow_add] at hna hnb
      have hv' : (amusicalPerm ^ (tm ((amusicalPerm ^ a) x) + a)) x =
          (amusicalPerm ^ (tm ((amusicalPerm ^ b) x) + b)) x := by omega
      have := hinj hv'
      omega
  have hMcard : M.card * (L - K + 1) ≤ 2 * (T + K + (L - K)) + 1 := by
    apply windowMin_card_mul_le M
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.1
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.2
  have hTL : T + K + (L - K) = T + L := by omega
  rw [hTL] at hMcard
  calc
    (L - K + 1) * F.card = (L - K + 1) * H.card + (L - K + 1) * G.card := by
      rw [← hsplit, Nat.mul_add]
    _ ≤ (L - K + 1) * Nat.count E X + (L - K + 1) * (M.card * (2 * K + 1)) := by
      gcongr
    _ = (L - K + 1) * Nat.count E X + (2 * K + 1) * (M.card * (L - K + 1)) := by ring
    _ ≤ (L - K + 1) * Nat.count E X + (2 * K + 1) * (2 * (T + L) + 1) := by gcongr

end CollatzMoonshot.Amusical
