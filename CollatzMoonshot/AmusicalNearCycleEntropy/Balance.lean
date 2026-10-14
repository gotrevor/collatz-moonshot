/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycleRuns

/-!
# Prefix balance (helpers for P2′)

`carry_potential_at` is MR I's carry potential (`NearCycleRuns.carry_potential`) with the scale
`x 0` replaced by a threshold `P` below every later point.  With `P = p + D` (every interior point
of a near-cycle excursion is `> p + D`) the carry of the first `t` steps is `≤ eRuns p t / (p + D)`;
since `x_t > p`, the log-drift `A log(3/2) − B log(4/3)` exceeds minus that carry.
-/

namespace CollatzMoonshot.Amusical.NearCycleRuns

open Finset

/-- **The carry potential at threshold `P`.**  `carry_potential` with the scale `x 0` replaced by
any `P ≥ 1` below every later point. -/
theorem carry_potential_at (x : ℕ → ℤ) (hE : ∀ k, Even (x k) → 2 * x (k + 1) = 3 * x k)
    (hO : ∀ k, Odd (x k) → 4 * x (k + 1) = 3 * x k + 1 ∨ 4 * x (k + 1) = 3 * x k - 1)
    {g : ℕ} {P : ℤ} (h0 : Even (x 0)) (hp : 1 ≤ x 0) (hP : 1 ≤ P)
    (hbig : ∀ k, 1 ≤ k → k ≤ g → P + 1 ≤ x k) :
    ∀ k ≤ g, ∃ s : ℝ, |Real.log (x k) - Real.log (x 0) -
        (k * Real.log 3 - (2 * k - cntE x k) * Real.log 2)| ≤ s ∧
      (P : ℝ) * s + 1 - (if Odd (x k) then (P : ℝ) / (x k - 1) else 0) ≤ cntR x (k + 1) := by
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
    have hxk : 1 ≤ x k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact hp
      · linarith [hbig k hk0 (by omega)]
    have hxk1 := hbig (k + 1) (by omega) hk
    have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
    have hXk : (1 : ℝ) ≤ x k := by exact_mod_cast hxk
    have hXk1 : (P : ℝ) + 1 ≤ x (k + 1) := by exact_mod_cast hxk1
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
      · have h1 : (0 : ℝ) ≤ (if Odd (x (k + 1)) then (P : ℝ) / (x (k + 1) - 1) else 0) := by
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
      have hxk' : P + 1 ≤ x k := hbig k (by omega) (by omega)
      have hXk' : (P : ℝ) + 1 ≤ x k := by exact_mod_cast hxk'
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
        have hdiv : (P : ℝ) / (x (k + 1) - 1) ≤ 1 := by
          rw [div_le_one (by linarith)]; linarith
        have hpt : (P : ℝ) * τ = P / (x (k + 1) - 1) - P / (x k - 1) := by
          rw [hτ]; ring
        by_cases hodd : Odd (x (k + 1))
        · rw [if_pos hodd, if_neg (fun h => (Int.not_even_iff_odd.mpr hodd) h.1)]
          push_cast
          nlinarith
        · rw [if_neg hodd, if_pos ⟨Int.not_odd_iff_even.mp hodd, ho⟩]
          push_cast
          nlinarith

/-- **P2′**, at any even point `x_t`, `0 < t < g` (the run need not start at `t`). -/
theorem prefix_balance' {D p g t : ℕ} (h : NearCycleAt D p g) (hp : 2 ≤ p)
    (ht : 0 < t) (htg : t < g) (hE : Even (amusical^[t] (p : ℤ))) :
    ((t - numE p t : ℕ) : ℝ) * Real.log (4 / 3) <
      (numE p t : ℝ) * Real.log (3 / 2) + (eRuns p t : ℝ) / (p + D) := by
  obtain ⟨s, hs, hpot⟩ := carry_potential_at (fun k => amusical^[k] (p : ℤ))
    (iterate_even_step _) (iterate_odd_step _) (g := t) (P := p + D) (nearCycleAt_even h)
    (by simp only [Function.iterate_zero, id_eq]; omega) (by omega)
    (fun k hk hkt => by have := h.2.2.2 k hk (by omega); omega) t le_rfl
  simp only [Function.iterate_zero, id_eq, Int.cast_natCast] at hs hpot
  rw [if_neg (Int.not_odd_iff_even.mpr hE)] at hpot
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hR : cntR (fun k => amusical^[k] (p : ℤ)) (t' + 1 + 1) ≤ eRuns p (t' + 1) + 1 := by
    rw [cntR_succ]; split_ifs <;> simp [eRuns, cntR]
  have hR' : (cntR (fun k => amusical^[k] (p : ℤ)) (t' + 1 + 1) : ℝ) ≤ eRuns p (t' + 1) + 1 := by
    exact_mod_cast hR
  replace hpot := hpot.trans hR'
  change (((p + D : ℤ) : ℝ)) * s + 1 - 0 ≤ (eRuns p (t' + 1) : ℝ) + 1 at hpot
  change |_ - _ - (_ - (2 * _ - ((numE p (t' + 1) : ℕ) : ℝ)) * _)| ≤ s at hs
  have hA : numE p (t' + 1) ≤ t' + 1 := cntE_le _ _
  rw [Nat.cast_sub hA]
  set A := numE p (t' + 1)
  set X : ℝ := ((amusical^[t' + 1] (p : ℤ) : ℤ) : ℝ) with hX
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hXp : (p : ℝ) < X := by
    have := h.2.2.2 (t' + 1) (by omega) htg
    rw [hX]; exact_mod_cast (by omega : (p : ℤ) < amusical^[t' + 1] (p : ℤ))
  have hlog : Real.log p < Real.log X := Real.log_lt_log hp0 hXp
  have hPD : (0 : ℝ) < p + D := by positivity
  have hs' : s ≤ (eRuns p (t' + 1) : ℝ) / (p + D) := by
    rw [le_div_iff₀ hPD]; push_cast at hpot; linarith
  rw [abs_le] at hs
  have h43 : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]; push_cast; ring
  have h32 : Real.log (3 / 2) = Real.log 3 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  rw [h43, h32]
  push_cast at hs ⊢
  nlinarith [hs.2]

/-- **P2′.**  See the module docstring. -/
theorem prefix_balance {D p g t : ℕ} (h : NearCycleAt D p g) (hp : 2 ≤ p)
    (ht : 0 < t) (htg : t < g) (_hO : Odd (amusical^[t - 1] (p : ℤ)))
    (hE : Even (amusical^[t] (p : ℤ))) :
    ((t - numE p t : ℕ) : ℝ) * Real.log (4 / 3) <
      (numE p t : ℝ) * Real.log (3 / 2) + (eRuns p t : ℝ) / (p + D) :=
  prefix_balance' h hp ht htg hE

end CollatzMoonshot.Amusical.NearCycleRuns
