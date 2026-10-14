/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycleLaw

/-!
# The run-by-run carry (helpers for MR I)

Everything is stated for an abstract integer sequence `x` obeying the two step laws of `U`:
`2 x' = 3 x` at an even point and `4 x' = 3 x ± 1` at an odd point.  `cntE x k` and `cntR x k`
are `numE` and `eRuns` for `x = (U^[·] p)` (definitionally).

* `odd_step_log`: an odd step `z ↦ z'` has carry `|log z' − log z − log(3/4)| ≤ 1/(3z − 1)`, and
  `1/(3z − 1) ≤ 1/(z' − 1) − 1/(z − 1)` (the telescoping form of `z − 1 ≥ (4/3)(z' − 1)`).
* `carry_bound`: if `x 0 = p` is even and every later point up to `g` is `≥ p + 1`, the total
  carry `s` satisfies `p s ≤ cntR x g`.  Proof: the potential
  `p s_k + 1 − [x_k odd] p/(x_k − 1) ≤ cntR x (k + 1)` is preserved step by step (an odd run
  telescopes; leaving it costs `p/(X − 1) ≤ 1` against the next `E`-run start).
-/

namespace CollatzMoonshot.Amusical.NearCycleRuns

open Finset

/-- `E`-steps among the first `k` terms. -/
def cntE (x : ℕ → ℤ) (k : ℕ) : ℕ := ((range k).filter fun t => Even (x t)).card

/-- `E`-run starts among the first `k` terms. -/
def cntR (x : ℕ → ℤ) (k : ℕ) : ℕ :=
  ((range k).filter fun t => Even (x t) ∧ (t = 0 ∨ Odd (x (t - 1)))).card

theorem cntE_succ (x : ℕ → ℤ) (k : ℕ) :
    cntE x (k + 1) = cntE x k + if Even (x k) then 1 else 0 := by
  unfold cntE
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem cntE_le (x : ℕ → ℤ) (k : ℕ) : cntE x k ≤ k :=
  (card_filter_le _ _).trans (card_range k).le

theorem cntR_one (x : ℕ → ℤ) : cntR x 1 = if Even (x 0) then 1 else 0 := by
  unfold cntR
  rw [range_one]
  by_cases h : Even (x 0)
  · rw [filter_singleton, if_pos ⟨h, Or.inl rfl⟩, if_pos h]; rfl
  · rw [filter_singleton, if_neg (fun h' => h h'.1), if_neg h]; rfl

theorem cntR_succ (x : ℕ → ℤ) (k : ℕ) :
    cntR x (k + 2) = cntR x (k + 1) + if Even (x (k + 1)) ∧ Odd (x k) then 1 else 0 := by
  unfold cntR
  rw [range_add_one (n := k + 1), filter_insert]
  have hiff : (Even (x (k + 1)) ∧ (k + 1 = 0 ∨ Odd (x (k + 1 - 1)))) ↔
      (Even (x (k + 1)) ∧ Odd (x k)) := by simp
  by_cases h : Even (x (k + 1)) ∧ Odd (x k)
  · rw [if_pos (hiff.mpr h), if_pos h, card_insert_of_notMem (by simp)]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]; rfl

theorem cntR_le_succ (x : ℕ → ℤ) (k : ℕ) : cntR x k ≤ cntR x (k + 1) := by
  unfold cntR
  exact card_le_card (filter_subset_filter _ (range_subset_range.mpr (Nat.le_succ k)))

/-- The even step of `U`. -/
theorem two_mul_amusical_of_even {x : ℤ} (h : Even x) : 2 * amusical x = 3 * x := by
  obtain ⟨n, rfl⟩ := h
  unfold amusical; split_ifs <;> omega

/-- The odd step of `U`: `4 U x = 3 x + 1` (`x ≡ 1 mod 4`) or `3 x − 1` (`x ≡ 3 mod 4`). -/
theorem four_mul_amusical_of_odd {x : ℤ} (h : Odd x) :
    4 * amusical x = 3 * x + 1 ∨ 4 * amusical x = 3 * x - 1 := by
  obtain ⟨n, rfl⟩ := h
  unfold amusical; split_ifs <;> omega

/-- `|log y| ≤ B` from the two one-sided bounds `log y ≤ y − 1`, `−log y ≤ y⁻¹ − 1`. -/
theorem abs_log_le {y B : ℝ} (hy : 0 < y) (h1 : y - 1 ≤ B) (h2 : y⁻¹ - 1 ≤ B) :
    |Real.log y| ≤ B := by
  rw [abs_le]
  refine ⟨?_, (Real.log_le_sub_one_of_pos hy).trans h1⟩
  have := Real.log_le_sub_one_of_pos (inv_pos.mpr hy)
  rw [Real.log_inv] at this
  linarith

/-- **The odd-step carry.**  For `4 z' = 3 z ± 1` with `z' ≥ 2`, the carry of the step is at most
`1/(z' − 1) − 1/(z − 1)`. -/
theorem odd_step_log {z z' : ℝ} (hz' : 2 ≤ z') (hstep : 4 * z' = 3 * z + 1 ∨ 4 * z' = 3 * z - 1) :
    |Real.log z' - Real.log z - (Real.log 3 - 2 * Real.log 2)| ≤
      1 / (z' - 1) - 1 / (z - 1) := by
  have hz : 2 < z := by rcases hstep with h | h <;> linarith
  have hz0 : 0 < z := by linarith
  have hz'0 : 0 < z' := by linarith
  have hlog : Real.log z' - Real.log z - (Real.log 3 - 2 * Real.log 2) =
      Real.log (4 * z' / (3 * z)) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by norm_num) (by positivity),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hkey : 1 / (3 * z - 1) ≤ 1 / (z' - 1) - 1 / (z - 1) := by
    rw [le_sub_iff_add_le, div_add_div _ _ (by linarith) (by linarith),
      div_le_div_iff₀ (by nlinarith) (by linarith)]
    rcases hstep with h | h <;> nlinarith
  rw [hlog]
  refine abs_log_le (by positivity) ?_ ?_ |>.trans hkey
  · rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) (by linarith)]
    rcases hstep with h | h <;> nlinarith
  · rw [inv_div, div_sub_one (by positivity), div_le_div_iff₀ (by positivity) (by linarith)]
    rcases hstep with h | h <;> nlinarith

/-- **The carry potential.**  See the module docstring. -/
theorem carry_potential (x : ℕ → ℤ) (hE : ∀ k, Even (x k) → 2 * x (k + 1) = 3 * x k)
    (hO : ∀ k, Odd (x k) → 4 * x (k + 1) = 3 * x k + 1 ∨ 4 * x (k + 1) = 3 * x k - 1)
    {g : ℕ} (h0 : Even (x 0)) (hp : 1 ≤ x 0) (hbig : ∀ k, 1 ≤ k → k ≤ g → x 0 + 1 ≤ x k) :
    ∀ k ≤ g, ∃ s : ℝ, |Real.log (x k) - Real.log (x 0) -
        (k * Real.log 3 - (2 * k - cntE x k) * Real.log 2)| ≤ s ∧
      (x 0 : ℝ) * s + 1 - (if Odd (x k) then (x 0 : ℝ) / (x k - 1) else 0) ≤ cntR x (k + 1) := by
  have hp' : (1 : ℝ) ≤ x 0 := by exact_mod_cast hp
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, by simp [cntE], ?_⟩
    rw [cntR_one, if_pos h0, if_neg (Int.not_odd_iff_even.mpr h0)]
    simp
  | succ k ih =>
    intro hk
    obtain ⟨s, hs, hpot⟩ := ih (by omega)
    have hxk : x 0 ≤ x k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact le_rfl
      · linarith [hbig k hk0 (by omega)]
    have hxk1 := hbig (k + 1) (by omega) hk
    have hXk : (x 0 : ℝ) ≤ x k := by exact_mod_cast hxk
    have hXk1 : (x 0 : ℝ) + 1 ≤ x (k + 1) := by exact_mod_cast hxk1
    have hXk0 : (0 : ℝ) < x k := by linarith
    have hXk10 : (0 : ℝ) < x (k + 1) := by linarith
    rcases Int.even_or_odd (x k) with he | ho
    · -- an `E`-step: no carry
      have hstep : (x (k + 1) : ℝ) = 3 * x k / 2 := by
        have := hE k he
        rw [eq_div_iff (by norm_num)]
        exact_mod_cast (by linarith : x (k + 1) * 2 = 3 * x k)
      have hlog : Real.log (x (k + 1)) = Real.log 3 + Real.log (x k) - Real.log 2 := by
        rw [hstep, Real.log_div (by positivity) (by norm_num),
          Real.log_mul (by norm_num) (by positivity)]
      refine ⟨s, ?_, ?_⟩
      · rw [hlog, cntE_succ, if_pos he]
        convert hs using 2
        push_cast; ring
      · have h1 : (0 : ℝ) ≤ (if Odd (x (k + 1)) then (x 0 : ℝ) / (x (k + 1) - 1) else 0) := by
          split_ifs
          · exact div_nonneg (by linarith) (by linarith)
          · exact le_rfl
        rw [if_neg (Int.not_odd_iff_even.mpr he)] at hpot
        have hR : (cntR x (k + 1) : ℝ) ≤ cntR x (k + 1 + 1) := by
          exact_mod_cast cntR_le_succ x (k + 1)
        linarith
    · -- an odd step: carry bounded by the telescoping difference
      have hk0 : k ≠ 0 := by
        rintro rfl; exact (Int.not_odd_iff_even.mpr h0) ho
      have hxk' : x 0 + 1 ≤ x k := hbig k (by omega) (by omega)
      have hXk' : (x 0 : ℝ) + 1 ≤ x k := by exact_mod_cast hxk'
      have hstep : 4 * (x (k + 1) : ℝ) = 3 * x k + 1 ∨ 4 * (x (k + 1) : ℝ) = 3 * x k - 1 := by
        rcases hO k ho with h | h
        · left; exact_mod_cast h
        · right; exact_mod_cast h
      have hc := odd_step_log (by linarith) hstep
      set τ := 1 / ((x (k + 1) : ℝ) - 1) - 1 / ((x k : ℝ) - 1) with hτ
      refine ⟨s + τ, ?_, ?_⟩
      · rw [cntE_succ, if_neg (Int.not_even_iff_odd.mpr ho)]
        have := abs_add_le (Real.log (x k) - Real.log (x 0) -
          (k * Real.log 3 - (2 * k - cntE x k) * Real.log 2))
          (Real.log (x (k + 1)) - Real.log (x k) - (Real.log 3 - 2 * Real.log 2))
        push_cast
        calc _ = |Real.log (x k) - Real.log (x 0) -
              (k * Real.log 3 - (2 * k - cntE x k) * Real.log 2) +
              (Real.log (x (k + 1)) - Real.log (x k) - (Real.log 3 - 2 * Real.log 2))| := by
                congr 1; ring
          _ ≤ s + τ := by linarith
      · rw [if_pos ho] at hpot
        rw [cntR_succ]
        have hdiv : (x 0 : ℝ) / (x (k + 1) - 1) ≤ 1 := by
          rw [div_le_one (by linarith)]; linarith
        have hpt : (x 0 : ℝ) * τ = x 0 / (x (k + 1) - 1) - x 0 / (x k - 1) := by
          rw [hτ]; ring
        by_cases hodd : Odd (x (k + 1))
        · rw [if_pos hodd, if_neg (fun h => (Int.not_even_iff_odd.mpr hodd) h.1)]
          push_cast
          nlinarith
        · rw [if_neg hodd, if_pos ⟨Int.not_odd_iff_even.mp hodd, ho⟩]
          push_cast
          nlinarith

/-- **The carry bound.**  The total carry `s` of the first `g` steps satisfies
`p s ≤ cntR x g`. -/
theorem carry_bound (x : ℕ → ℤ) (hE : ∀ k, Even (x k) → 2 * x (k + 1) = 3 * x k)
    (hO : ∀ k, Odd (x k) → 4 * x (k + 1) = 3 * x k + 1 ∨ 4 * x (k + 1) = 3 * x k - 1)
    {g : ℕ} (hg : 1 ≤ g) (h0 : Even (x 0)) (hp : 1 ≤ x 0)
    (hbig : ∀ k, 1 ≤ k → k ≤ g → x 0 + 1 ≤ x k) :
    ∃ s : ℝ, |Real.log (x g) - Real.log (x 0) -
        (g * Real.log 3 - (2 * g - cntE x g) * Real.log 2)| ≤ s ∧
      (x 0 : ℝ) * s ≤ cntR x g := by
  obtain ⟨s, hs, hpot⟩ := carry_potential x hE hO h0 hp hbig g le_rfl
  refine ⟨s, hs, ?_⟩
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  rw [cntR_succ] at hpot
  have hX : (x 0 : ℝ) + 1 ≤ x (g' + 1) := by exact_mod_cast hbig (g' + 1) hg le_rfl
  have hp' : (1 : ℝ) ≤ x 0 := by exact_mod_cast hp
  by_cases hodd : Odd (x (g' + 1))
  · rw [if_pos hodd, if_neg (fun h => (Int.not_even_iff_odd.mpr hodd) h.1)] at hpot
    have hdiv : (x 0 : ℝ) / (x (g' + 1) - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    push_cast at hpot
    linarith
  · rw [if_neg hodd] at hpot
    have : ((if Even (x (g' + 1)) ∧ Odd (x g') then 1 else 0 : ℕ) : ℝ) ≤ 1 := by
      split_ifs <;> norm_num
    push_cast at hpot this ⊢
    linarith

/-! ### The orbit of a near-cycle start -/

theorem iterate_even_step (p : ℤ) (k : ℕ) (h : Even (amusical^[k] p)) :
    2 * amusical^[k + 1] p = 3 * amusical^[k] p := by
  rw [Function.iterate_succ_apply']; exact two_mul_amusical_of_even h

theorem iterate_odd_step (p : ℤ) (k : ℕ) (h : Odd (amusical^[k] p)) :
    4 * amusical^[k + 1] p = 3 * amusical^[k] p + 1 ∨
      4 * amusical^[k + 1] p = 3 * amusical^[k] p - 1 := by
  rw [Function.iterate_succ_apply']; exact four_mul_amusical_of_odd h

/-- A near-cycle start moves up at its first step. -/
theorem nearCycleAt_lt_amusical {D p g : ℕ} (h : NearCycleAt D p g) :
    (p : ℤ) < amusical p := by
  obtain ⟨hg, h1, -, h3⟩ := h
  rcases Nat.lt_or_ge 1 g with hg1 | hg1
  · have := h3 1 le_rfl hg1
    simp only [Function.iterate_one] at this
    omega
  · obtain rfl : g = 1 := by omega
    simpa using h1

/-- A near-cycle start is `≥ 2` (`0` and `1` are fixed). -/
theorem nearCycleAt_two_le {D p g : ℕ} (h : NearCycleAt D p g) : 2 ≤ p := by
  have h1 := nearCycleAt_lt_amusical h
  by_contra hp
  interval_cases p <;> simp [amusical] at h1

/-- A near-cycle start is even (an odd `p ≥ 2` has `U p < p`). -/
theorem nearCycleAt_even {D p g : ℕ} (h : NearCycleAt D p g) : Even (p : ℤ) := by
  have h1 := nearCycleAt_lt_amusical h
  have h2 := nearCycleAt_two_le h
  by_contra ho
  rcases four_mul_amusical_of_odd (Int.not_even_iff_odd.mp ho) with h4 | h4 <;> omega

/-- Every later point of the excursion, up to the return, is `≥ p + 1`. -/
theorem nearCycleAt_big {D p g : ℕ} (h : NearCycleAt D p g) :
    ∀ k, 1 ≤ k → k ≤ g → (p : ℤ) + 1 ≤ amusical^[k] (p : ℤ) := by
  obtain ⟨-, h1, -, h3⟩ := h
  intro k hk hkg
  rcases Nat.lt_or_ge k g with hlt | hge
  · have := h3 k hk hlt; omega
  · obtain rfl : k = g := by omega
    omega

end CollatzMoonshot.Amusical.NearCycleRuns
