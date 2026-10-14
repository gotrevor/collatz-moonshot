/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The fair binomial lower tail (helper for the Chernoff target)

`α = j / n ≤ 1/2`: `Σ_{i ≤ j} C(n, i) α^j (1 − α)^{n − j} ≤ Σ_i C(n, i) α^i (1 − α)^{n − i} = 1`,
and `α^j (1 − α)^{n − j} = exp(−n H(α))`.
-/

namespace CollatzMoonshot.Amusical.NearCycleEntropy

open Finset

/-- **Chernoff.** -/
theorem sum_choose_le_exp (n j : ℕ) (hj : 2 * j ≤ n) :
    (∑ i ∈ range (j + 1), (n.choose i : ℝ)) ≤
      Real.exp (n * Real.binEntropy ((j : ℝ) / n)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set α : ℝ := (j : ℝ) / n with hα
  have hα0 : 0 < α := div_pos (by exact_mod_cast hj0) hn
  have hα2 : α ≤ 1 - α := by
    rw [hα, le_sub_iff_add_le, ← two_mul, mul_div_assoc', div_le_one hn]
    exact_mod_cast hj
  have hα1 : 0 < 1 - α := by linarith
  set q : ℝ := α ^ j * (1 - α) ^ (n - j) with hq
  have hq0 : 0 < q := by positivity
  have hexp : Real.exp (n * Real.binEntropy α) = q⁻¹ := by
    have hnα : (n : ℝ) * α = j := by rw [hα]; field_simp
    have hnj : ((n - j : ℕ) : ℝ) = n * (1 - α) := by
      rw [Nat.cast_sub (by omega)]; rw [mul_sub, hnα]; ring
    rw [Real.binEntropy, mul_add, ← mul_assoc, ← mul_assoc, hnα, ← hnj, Real.log_inv,
      Real.log_inv, ← Real.exp_log (inv_pos.mpr hq0), Real.log_inv, hq,
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring_nf
  rw [hexp, ← one_div, le_div_iff₀ hq0, sum_mul]
  have hterm : ∀ i ∈ range (j + 1), (n.choose i : ℝ) * q ≤
      α ^ i * (1 - α) ^ (n - i) * (n.choose i : ℝ) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have h1 : α ^ j = α ^ i * α ^ (j - i) := by rw [← pow_add]; congr 1; omega
    have h2 : (1 - α) ^ (n - i) = (1 - α) ^ (j - i) * (1 - α) ^ (n - j) := by
      rw [← pow_add]; congr 1; omega
    rw [hq, h1, h2]
    have h3 : α ^ (j - i) ≤ (1 - α) ^ (j - i) := pow_le_pow_left₀ hα0.le hα2 _
    calc α ^ i * α ^ (j - i) * (1 - α) ^ (n - j)
        ≤ α ^ i * (1 - α) ^ (j - i) * (1 - α) ^ (n - j) := by gcongr
      _ = _ := by ring
  calc _ ≤ ∑ i ∈ range (j + 1), α ^ i * (1 - α) ^ (n - i) * (n.choose i : ℝ) := sum_le_sum hterm
    _ ≤ ∑ i ∈ range (n + 1), α ^ i * (1 - α) ^ (n - i) * (n.choose i : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
          (fun _ _ _ => by positivity)
    _ = (α + (1 - α)) ^ n := (add_pow _ _ _).symm
    _ = 1 := by simp

end CollatzMoonshot.Amusical.NearCycleEntropy
