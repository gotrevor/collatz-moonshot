/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycleEntropy.Balance
import CollatzMoonshot.AmusicalNearCycleEntropy.Word

/-!
# The stopped prefix of a near-cycle excursion (helper for RT-low)

If the excursion of `p` has at least `τ ≥ 1` `E`-steps, cut it at its `τ`-th `E`, at time `t`.  The
pattern `pat (t + 1) p` starts and ends with `E`, has `τ` `E`'s, at most `eRuns p g` runs, and
(P2′ at `t`) `#O · log(4/3) < (τ − 1) log(3/2) + 1` once `eRuns p g ≤ p + D`.
-/

namespace CollatzMoonshot.Amusical.NearCycleEntropy

open NearCycleRuns

theorem eRuns_mono (p : ℕ) {a b : ℕ} (h : a ≤ b) : eRuns p a ≤ eRuns p b :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

/-- **The stopped prefix.** -/
theorem exists_stopped {D p g τ : ℕ} (h : NearCycleAt D p g) (hτ1 : 1 ≤ τ)
    (hτ : τ ≤ numE p g) (hmD : eRuns p g ≤ p + D) :
    ∃ t, t + 1 ≤ g ∧ (pat (t + 1) (p : ℤ)).head? = some true ∧
      (pat (t + 1) (p : ℤ)).getLast? = some true ∧ (pat (t + 1) (p : ℤ)).count true = τ ∧
      runs (pat (t + 1) (p : ℤ)) ≤ eRuns p g ∧
      ((pat (t + 1) (p : ℤ)).count false : ℝ) * Real.log (4 / 3) <
        ((τ : ℝ) - 1) * Real.log (3 / 2) + 1 := by
  have hp2 := nearCycleAt_two_le h
  have hex : ∃ t, τ ≤ numE p (t + 1) := ⟨g - 1, by rw [Nat.sub_add_cancel h.1]; exact hτ⟩
  set t := Nat.find hex with ht
  have htτ : τ ≤ numE p (t + 1) := Nat.find_spec hex
  have htg : t + 1 ≤ g := by
    have := Nat.find_min' hex (show τ ≤ numE p (g - 1 + 1) by
      rw [Nat.sub_add_cancel h.1]; exact hτ)
    rw [← ht] at this
    have := h.1
    omega
  have hlt : numE p t < τ := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0]; simp [numE]; omega
    · obtain ⟨t', ht'⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have := Nat.find_min hex (show t' < t by omega)
      rw [ht']; omega
  have hsucc := cntE_succ (fun i => amusical^[i] (p : ℤ)) t
  change numE p (t + 1) = numE p t + _ at hsucc
  have hEt : Even (amusical^[t] (p : ℤ)) := by
    by_contra hc
    rw [if_neg hc] at hsucc; omega
  rw [if_pos hEt] at hsucc
  have hcT : (pat (t + 1) (p : ℤ)).count true = τ := by
    rw [count_true_pat]; change numE p (t + 1) = τ; omega
  refine ⟨t, htg, ?_, ?_, hcT, ?_, ?_⟩
  · rw [head?_pat, decide_eq_true (nearCycleAt_even h)]
  · rw [getLast?_pat, decide_eq_true hEt]
  · rw [runs_pat]; exact eRuns_mono p htg
  · rw [count_false_pat]
    change (((t + 1 - numE p (t + 1) : ℕ)) : ℝ) * _ < _
    rw [show t + 1 - numE p (t + 1) = t - numE p t by omega]
    have hτR : (1 : ℝ) ≤ τ := by exact_mod_cast hτ1
    have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0]; simp only [Nat.zero_sub, CharP.cast_eq_zero, zero_mul]; nlinarith
    · have hb := prefix_balance' h hp2 h0 (by omega) hEt
      have hnE : (numE p t : ℝ) = τ - 1 := by
        rw [show numE p t = τ - 1 by omega, Nat.cast_sub hτ1]; simp
      have hfrac : (eRuns p t : ℝ) / (p + D) ≤ 1 := by
        have hpos : (0 : ℝ) < p + D := by positivity
        rw [div_le_one hpos]
        exact_mod_cast (eRuns_mono p (by omega : t ≤ g)).trans hmD
      rw [hnE] at hb
      linarith
