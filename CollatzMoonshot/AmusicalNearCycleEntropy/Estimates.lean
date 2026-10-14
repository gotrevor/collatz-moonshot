/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Exponent bookkeeping (helpers for RT-low)

With `L = log₂ D`, `τ ≥ L/4`, `m ≤ L/40`, `M ≤ 1.41 τ + 4`:

* `sum_choose_lt_le`: `Σ_{i<m} C(n, i) ≤ 9^m (10/9)^n` (the binomial theorem at `α = 1/10`);
* `main_le`: `D L^14 9^m (5/9)^τ ≤ K D^0.87` (`100 log 5 + 53 log 2 ≤ 90 log 9`, so the exponent
  is `347/400` plus `1/400` for `L^14`);
* `tail_le`: `2^M 81^m (10/9)^{τ+M} ≤ K D^0.87` (the exponent is about `0.60`);
* `log_le`: `L + 1 ≤ K D^0.87`.

Every numerical input is an integer-power comparison closed by `norm_num`.
-/

namespace CollatzMoonshot.Amusical.NearCycleEntropy

open Finset

/-- `Σ_{i<m} C(n, i) ≤ 9^m (10/9)^n`. -/
theorem sum_choose_lt_le (n m : ℕ) :
    ∑ i ∈ range m, (n.choose i : ℝ) ≤ 9 ^ m * (10 / 9) ^ n := by
  set f : ℕ → ℝ := fun i => (n.choose i : ℝ) * (1 / 10) ^ i * (9 / 10) ^ (n - i) with hf
  have hsum : ∑ i ∈ range m, f i ≤ 1 := by
    rw [← sum_filter_of_ne (p := fun i => i ≤ n) (fun i _ hi => by
      by_contra hc
      exact hi (by rw [hf]; simp [Nat.choose_eq_zero_of_lt (by omega : n < i)]))]
    calc _ ≤ ∑ i ∈ range (n + 1), f i :=
          sum_le_sum_of_subset_of_nonneg (fun i hi => by simp at hi ⊢; omega)
            (fun _ _ _ => by positivity)
      _ = (1 / 10 + 9 / 10 : ℝ) ^ n := by rw [add_pow]; simp only [hf]; congr 1; ext i; ring
      _ = 1 := by norm_num
  have hterm : ∀ i ∈ range m, (n.choose i : ℝ) * ((1 / 9) ^ m * (9 / 10) ^ n) ≤ f i := by
    intro i hi
    have him : i ≤ m := (mem_range.mp hi).le
    rcases le_or_gt i n with hin | hin
    · rw [hf]
      simp only
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 : ((1 : ℝ) / 9) ^ m ≤ (1 / 9) ^ i :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) him
      have h2 : ((1 : ℝ) / 10) ^ i * (9 / 10) ^ (n - i) = (1 / 9) ^ i * (9 / 10) ^ n := by
        rw [show n = i + (n - i) from (Nat.add_sub_cancel' hin).symm, pow_add,
          Nat.add_sub_cancel_left, ← mul_assoc, ← mul_pow]
        norm_num
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    · simp [Nat.choose_eq_zero_of_lt hin, hf]
  have := (sum_le_sum hterm).trans hsum
  rw [← sum_mul] at this
  have hpos : (0 : ℝ) < (1 / 9) ^ m * (9 / 10) ^ n := by positivity
  rw [← le_div_iff₀ hpos] at this
  refine this.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, one_mul, mul_inv, ← inv_pow, ← inv_pow]
  norm_num

theorem log_five_nine : 100 * Real.log 5 + 53 * Real.log 2 ≤ 90 * Real.log 9 := by
  have h : (5 : ℝ) ^ 100 * 2 ^ 53 ≤ 9 ^ 90 := by norm_num
  have := Real.log_le_log (by positivity) h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at this
  push_cast at this; linarith

set_option exponentiation.threshold 400 in
theorem log_tail : 141 * Real.log (20 / 9) + 10 * Real.log 81 + 100 * Real.log (10 / 9) ≤
    348 * Real.log 2 := by
  have h : ((20 : ℝ) / 9) ^ 141 * 81 ^ 10 * (10 / 9) ^ 100 ≤ 2 ^ 348 := by norm_num
  have := Real.log_le_log (by positivity) h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at this
  push_cast at this; linarith

theorem log_beta : 100 * Real.log (3 / 2) ≤ 141 * Real.log (4 / 3) := by
  have h : ((3 : ℝ) / 2) ^ 100 ≤ (4 / 3) ^ 141 := by norm_num
  have := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this; linarith

set_option exponentiation.threshold 400 in
theorem log_theta : 200 * Real.log 3 ≤ 317 * Real.log 2 := by
  have h : (3 : ℝ) ^ 200 ≤ 2 ^ 317 := by norm_num
  have := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at this
  push_cast at this; linarith

theorem quarter_le_log : (1 : ℝ) / 4 ≤ Real.log (4 / 3) := by
  have := Real.one_sub_inv_le_log_of_pos (x := 4 / 3) (by norm_num)
  norm_num at this ⊢; linarith

/-- `log L ≤ log (5600 / log 2) + log D / 5600`. -/
theorem log_logb_le {D : ℝ} (hD : 2 ≤ D) :
    Real.log (Real.logb 2 D) ≤ Real.log (5600 / Real.log 2) + Real.log D / 5600 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓ : 0 < Real.log D := Real.log_pos (by linarith)
  have h1 := Real.log_le_sub_one_of_pos (x := Real.log D / 5600) (by positivity)
  rw [Real.log_div hℓ.ne' (by norm_num)] at h1
  rw [Real.logb, Real.log_div hℓ.ne' hl2.ne', Real.log_div (by norm_num) hl2.ne']
  linarith

theorem one_le_logb {D : ℝ} (hD : 2 ≤ D) : 1 ≤ Real.logb 2 D := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hD

/-- **The main term.** -/
theorem main_le : ∃ K : ℝ, ∀ D : ℝ, 2 ≤ D → ∀ τ m : ℕ, Real.logb 2 D / 4 ≤ τ →
    (m : ℝ) ≤ Real.logb 2 D / 40 →
    D * Real.logb 2 D ^ 14 * 9 ^ m * (5 / 9) ^ τ ≤ K * D ^ (0.87 : ℝ) := by
  refine ⟨(5600 / Real.log 2) ^ 14, fun D hD τ m hτ hm => ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD0 : 0 < D := by linarith
  have hL := one_le_logb hD
  have hlogL := log_logb_le hD
  have hLℓ : Real.logb 2 D * Real.log 2 = Real.log D := by
    rw [Real.logb, div_mul_cancel₀ _ hl2.ne']
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_rpow hD0,
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  have h59 : Real.log (5 / 9) = Real.log 5 - Real.log 9 := Real.log_div (by norm_num) (by norm_num)
  have h59n : Real.log (5 / 9) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have h9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hA : (m : ℝ) * Real.log 9 ≤ Real.logb 2 D / 40 * Real.log 9 :=
    mul_le_mul_of_nonneg_right hm h9.le
  have hB : (τ : ℝ) * Real.log (5 / 9) ≤ Real.logb 2 D / 4 * Real.log (5 / 9) :=
    mul_le_mul_of_nonpos_right hτ h59n.le
  have hC := log_five_nine
  have hE : Real.logb 2 D * (100 * Real.log 5 + 53 * Real.log 2) ≤
      Real.logb 2 D * (90 * Real.log 9) := mul_le_mul_of_nonneg_left hC (by linarith)
  push_cast
  rw [h59] at hB
  nlinarith

/-- **The tail term.** -/
theorem tail_le : ∃ K : ℝ, ∀ D : ℝ, 2 ≤ D → ∀ τ m M : ℕ, (τ : ℝ) ≤ Real.logb 2 D / 4 + 1 →
    (m : ℝ) ≤ Real.logb 2 D / 40 → (M : ℝ) ≤ 1.41 * τ + 4 →
    2 ^ M * 81 ^ m * (10 / 9) ^ (τ + M) ≤ K * D ^ (0.87 : ℝ) := by
  refine ⟨Real.exp (6 * Real.log (20 / 9) + Real.log (10 / 9)), fun D hD τ m M hτ hm hM => ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD0 : 0 < D := by linarith
  have hL := one_le_logb hD
  have hLℓ : Real.logb 2 D * Real.log 2 = Real.log D := by
    rw [Real.logb, div_mul_cancel₀ _ hl2.ne']
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_rpow hD0, Real.log_exp, Real.log_pow, Real.log_pow, Real.log_pow]
  have h209 : Real.log (20 / 9) = Real.log 2 + Real.log (10 / 9) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h109 : 0 < Real.log (10 / 9) := Real.log_pos (by norm_num)
  have h81 : 0 < Real.log 81 := Real.log_pos (by norm_num)
  have hA : (m : ℝ) * Real.log 81 ≤ Real.logb 2 D / 40 * Real.log 81 :=
    mul_le_mul_of_nonneg_right hm h81.le
  have hM' : (M : ℝ) * Real.log (20 / 9) ≤ (1.41 * τ + 4) * Real.log (20 / 9) :=
    mul_le_mul_of_nonneg_right hM (by rw [h209]; positivity)
  have hτ' : (τ : ℝ) * (1.41 * Real.log (20 / 9) + Real.log (10 / 9)) ≤
      (Real.logb 2 D / 4 + 1) * (1.41 * Real.log (20 / 9) + Real.log (10 / 9)) :=
    mul_le_mul_of_nonneg_right hτ (by rw [h209]; positivity)
  have hC := log_tail
  have hE : Real.logb 2 D * (141 * Real.log (20 / 9) + 10 * Real.log 81 +
      100 * Real.log (10 / 9)) ≤ Real.logb 2 D * (348 * Real.log 2) :=
    mul_le_mul_of_nonneg_left hC (by linarith)
  push_cast
  rw [h209] at hM' hτ' hE ⊢
  nlinarith

/-- **The small starts.** -/
theorem logb_add_one_le : ∃ K : ℝ, ∀ D : ℝ, 2 ≤ D →
    Real.logb 2 D + 1 ≤ K * D ^ (0.87 : ℝ) := by
  refine ⟨2 * (5600 / Real.log 2), fun D hD => ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD0 : 0 < D := by linarith
  have hL := one_le_logb hD
  have hlogL := log_logb_le hD
  have h1 : Real.logb 2 D ≤ 5600 / Real.log 2 * D ^ (0.87 : ℝ) := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_rpow hD0]
    have hℓ : 0 < Real.log D := Real.log_pos (by linarith)
    linarith
  have h2 : 1 ≤ D ^ (0.87 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have h3 : 1 ≤ 5600 / Real.log 2 := by
    rw [le_div_iff₀ hl2]; linarith [Real.log_two_lt_d9]
  nlinarith

end CollatzMoonshot.Amusical.NearCycleEntropy
