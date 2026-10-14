/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycleRuns.Carry

/-!
# Run growth (helpers for MR II, upper half)

For a sequence obeying the step laws of `U` and staying `≥ 2`, with `θ = log₂ 3`, `c = log₂ x₀`
and `r = cntR x (k + 1)`, write `x_k = 2^v o` (`o` odd).  Then (`numE_potential`)

* `(cntE x k + v)(θ − 1) ≤ c (θ^r − 1)`, and
* `log₂ x_k + v (θ − 1) ≤ c θ^r`.

An `E`-step trades one unit of `v` for one `E`-step and multiplies `x` by `3/2`, so both lines are
unchanged.  An odd step decreases `x`; when it lands on an even point a new `E`-run starts, whose
budget `v ≤ log₂ x` is paid by the second line (`log₂ x ≤ c θ^r`), and its peak by `θ log₂ x`.
-/

namespace CollatzMoonshot.Amusical.NearCycleRuns

open Finset

/-- A positive integer is `2^v` times an odd number. -/
theorem exists_two_pow_mul_odd {z : ℤ} (hz : 0 < z) : ∃ (v : ℕ) (o : ℤ), Odd o ∧ z = 2 ^ v * o := by
  obtain ⟨v, m, hm, hzm⟩ := Nat.exists_eq_two_pow_mul_odd (n := z.toNat) (by omega)
  refine ⟨v, m, ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := hm; exact ⟨j, by push_cast; ring⟩
  · have : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz.le
    rw [← this, hzm]; push_cast; ring

/-- The `2`-adic budget is at most `log₂`. -/
theorem le_logb_of_two_pow_mul {z : ℤ} {v : ℕ} {o : ℤ} (hz : 0 < z) (h : z = 2 ^ v * o) :
    (v : ℝ) ≤ Real.logb 2 z := by
  have ho : 1 ≤ o := by
    by_contra ho
    have : 2 ^ v * o ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    omega
  have h2 : ((2 : ℝ) ^ v) ≤ z := by
    have : (2 : ℤ) ^ v ≤ z := by rw [h]; exact le_mul_of_one_le_right (by positivity) ho
    exact_mod_cast this
  calc (v : ℝ) = Real.logb 2 ((2 : ℝ) ^ v) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    _ ≤ Real.logb 2 z := Real.logb_le_logb_of_le (by norm_num) (by positivity) h2

theorem one_lt_logb_two_three : 1 < Real.logb 2 3 := by
  rw [Real.logb, one_lt_div (Real.log_pos (by norm_num))]
  exact Real.log_lt_log (by norm_num) (by norm_num)

theorem odd_iff_two_pow_mul {z o : ℤ} {v : ℕ} (ho : Odd o) (h : z = 2 ^ v * o) :
    Odd z ↔ v = 0 := by
  constructor
  · intro hz
    by_contra hv
    obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
    rw [h, pow_succ, mul_comm _ 2, mul_assoc] at hz
    exact (Int.not_odd_iff_even.mpr (even_two_mul _)) hz
  · rintro rfl; simpa [h] using ho

/-- **The run-growth potential.**  See the module docstring. -/
theorem numE_potential (x : ℕ → ℤ) (hE : ∀ k, Even (x k) → 2 * x (k + 1) = 3 * x k)
    (hO : ∀ k, Odd (x k) → 4 * x (k + 1) = 3 * x k + 1 ∨ 4 * x (k + 1) = 3 * x k - 1)
    {g : ℕ} (h2 : ∀ k ≤ g, 2 ≤ x k) :
    ∀ k < g, ∃ (v : ℕ) (o : ℤ), Odd o ∧ x k = 2 ^ v * o ∧
      ((cntE x k : ℝ) + v) * (Real.logb 2 3 - 1) ≤
        Real.logb 2 (x 0) * (Real.logb 2 3 ^ cntR x (k + 1) - 1) ∧
      Real.logb 2 (x k) + v * (Real.logb 2 3 - 1) ≤
        Real.logb 2 (x 0) * Real.logb 2 3 ^ cntR x (k + 1) := by
  set θ := Real.logb 2 3 with hθ
  set c := Real.logb 2 (x 0) with hc
  have hθ1 : 1 < θ := one_lt_logb_two_three
  have hb : (1 : ℝ) < 2 := by norm_num
  intro k
  induction k with
  | zero =>
    intro hg
    obtain ⟨v, o, ho, hx⟩ := exists_two_pow_mul_odd (by linarith [h2 0 (by omega)] : 0 < x 0)
    have hv := le_logb_of_two_pow_mul (by linarith [h2 0 (by omega)]) hx
    refine ⟨v, o, ho, hx, ?_⟩
    rw [cntR_one]
    by_cases he : Even (x 0)
    · rw [if_pos he, pow_one]
      simp only [cntE, range_zero, filter_empty, card_empty, CharP.cast_eq_zero, zero_add]
      constructor
      · exact mul_le_mul_of_nonneg_right hv (by linarith)
      · nlinarith
    · rw [if_neg he, pow_zero]
      have hv0 : v = 0 := (odd_iff_two_pow_mul ho hx).mp (Int.not_even_iff_odd.mp he)
      subst hv0
      simp [cntE, hc]
  | succ k ih =>
    intro hk
    obtain ⟨v, o, ho, hx, hA, hB⟩ := ih (by omega)
    have hxk : (2 : ℝ) ≤ x k := by exact_mod_cast h2 k (by omega)
    have hxk1 : (2 : ℝ) ≤ x (k + 1) := by exact_mod_cast h2 (k + 1) (by omega)
    rcases Int.even_or_odd (x k) with he | hodd
    · -- an `E`-step
      have hv : v ≠ 0 := fun hv => (Int.not_odd_iff_even.mpr he)
        ((odd_iff_two_pow_mul ho hx).mpr hv)
      obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      have hstep := hE k he
      have hx1 : x (k + 1) = 2 ^ w * (3 * o) := by
        rw [hx, pow_succ] at hstep; linarith
      have hstepR : (x (k + 1) : ℝ) = x k * 3 / 2 := by
        rw [eq_div_iff (by norm_num)]; exact_mod_cast (by linarith : x (k + 1) * 2 = x k * 3)
      have hlog : Real.logb 2 (x (k + 1)) = Real.logb 2 (x k) + θ - 1 := by
        rw [hstepR, Real.logb_div (by positivity) (by norm_num),
          Real.logb_mul (by positivity) (by norm_num), Real.logb_self_eq_one hb]
      refine ⟨w, 3 * o, Odd.mul (by decide) ho, hx1, ?_⟩
      rw [cntR_succ, if_neg (fun h => (Int.not_odd_iff_even.mpr he) h.2), add_zero, cntE_succ,
        if_pos he, hlog]
      push_cast at hA hB ⊢
      constructor <;> linarith
    · -- an odd step
      have hv0 : v = 0 := (odd_iff_two_pow_mul ho hx).mp hodd
      subst hv0
      have hlt : (x (k + 1) : ℝ) < x k := by
        have : x (k + 1) < x k := by
          have := h2 k (by omega)
          rcases hO k hodd with h | h <;> omega
        exact_mod_cast this
      have hlog : Real.logb 2 (x (k + 1)) < Real.logb 2 (x k) :=
        Real.logb_lt_logb hb (by linarith) hlt
      have hlog0 : 0 ≤ Real.logb 2 (x (k + 1)) :=
        Real.logb_nonneg hb (by linarith)
      rw [cntE_succ, if_neg (Int.not_even_iff_odd.mpr hodd), add_zero]
      simp only [CharP.cast_eq_zero, add_zero, zero_mul] at hA hB
      obtain ⟨v', o', ho', hx'⟩ := exists_two_pow_mul_odd
        (by exact_mod_cast (by linarith : (0 : ℝ) < x (k + 1)) : 0 < x (k + 1))
      have hv' := le_logb_of_two_pow_mul
        (by exact_mod_cast (by linarith : (0 : ℝ) < x (k + 1))) hx'
      refine ⟨v', o', ho', hx', ?_⟩
      by_cases he' : Even (x (k + 1))
      · rw [cntR_succ, if_pos ⟨he', hodd⟩, pow_succ]
        set T := θ ^ cntR x (k + 1)
        have hcT : Real.logb 2 (x (k + 1)) ≤ c * T := by linarith
        have h1 : (v' : ℝ) * (θ - 1) ≤ c * T * (θ - 1) :=
          mul_le_mul_of_nonneg_right (hv'.trans hcT) (by linarith)
        have h3 : Real.logb 2 (x (k + 1)) * (θ - 1) ≤ c * T * (θ - 1) :=
          mul_le_mul_of_nonneg_right hcT (by linarith)
        constructor <;> nlinarith
      · have hv'0 : v' = 0 :=
          (odd_iff_two_pow_mul ho' hx').mp (Int.not_even_iff_odd.mp he')
        subst hv'0
        rw [cntR_succ, if_neg (fun h => he' h.1), add_zero]
        simp only [CharP.cast_eq_zero, add_zero, zero_mul]
        exact ⟨hA, by linarith⟩

/-- **Few runs force few `E`-steps.** -/
theorem cntE_le_of_runs (x : ℕ → ℤ) (hE : ∀ k, Even (x k) → 2 * x (k + 1) = 3 * x k)
    (hO : ∀ k, Odd (x k) → 4 * x (k + 1) = 3 * x k + 1 ∨ 4 * x (k + 1) = 3 * x k - 1)
    {g : ℕ} (hg : 1 ≤ g) (h2 : ∀ k ≤ g, 2 ≤ x k) :
    (cntE x g : ℝ) ≤
      Real.logb 2 (x 0) * (Real.logb 2 3 ^ cntR x g - 1) / (Real.logb 2 3 - 1) := by
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  obtain ⟨v, o, ho, hx, hA, -⟩ := numE_potential x hE hO h2 g' (by omega)
  have hθ1 := one_lt_logb_two_three
  rw [le_div_iff₀ (by linarith), cntE_succ]
  have hev : ((if Even (x g') then 1 else 0 : ℕ) : ℝ) ≤ v := by
    split_ifs with he
    · have hv : v ≠ 0 := fun hv => (Int.not_odd_iff_even.mpr he)
        ((odd_iff_two_pow_mul ho hx).mpr hv)
      have : 1 ≤ v := by omega
      push_cast; exact_mod_cast this
    · push_cast; positivity
  push_cast at hev ⊢
  nlinarith

end CollatzMoonshot.Amusical.NearCycleRuns
