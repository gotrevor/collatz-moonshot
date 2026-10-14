/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycleRuns.Growth

/-!
# The bootstrap (helpers for MR-P)

* `rpow_bootstrap`: `p ≤ M D (A (log p + 1))^13.3` implies `p ≤ C D (log D + 1)^13.3`.  Since
  `log p + 1 ≤ 27.6 p^{1/26.6}`, the hypothesis gives `√p ≤ M D G`, so `log p ≤ 2 log (M D G)`,
  which is `O(log D + 1)`; substitute back.
* `two_mul_le_growthConst`: MR II's two halves give `2 g ≤ A_m (log p + 1)` with
  `A_m = 2 (1 + K_m / log 2)/(2 − θ)`, `K_m = (θ^m − 1)/(θ − 1)`.
-/

namespace CollatzMoonshot.Amusical.NearCycleRuns

/-- `θ = log₂ 3 < 2`. -/
theorem logb_two_three_lt_two : Real.logb 2 3 < 2 := by
  rw [Real.logb, div_lt_iff₀ (Real.log_pos (by norm_num)), ← Real.log_rpow (by norm_num)]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- `K_m = (θ^m − 1)/(θ − 1)`. -/
noncomputable def runConst (m : ℕ) : ℝ := (Real.logb 2 3 ^ m - 1) / (Real.logb 2 3 - 1)

/-- `A_m = 2 (1 + K_m / log 2)/(2 − θ)`. -/
noncomputable def growthConst (m : ℕ) : ℝ :=
  2 * (1 + runConst m / Real.log 2) / (2 - Real.logb 2 3)

theorem runConst_nonneg (m : ℕ) : 0 ≤ runConst m := by
  have h := one_lt_logb_two_three
  exact div_nonneg (by linarith [one_le_pow₀ (n := m) h.le]) (by linarith)

theorem one_le_growthConst (m : ℕ) : 1 ≤ growthConst m := by
  have h1 := one_lt_logb_two_three
  have h2 := logb_two_three_lt_two
  have hK : 0 ≤ runConst m / Real.log 2 :=
    div_nonneg (runConst_nonneg m) (Real.log_pos (by norm_num)).le
  rw [growthConst, le_div_iff₀ (by linarith)]
  linarith

/-- **The return-time bound.**  From MR II: `2 g ≤ A_m (log p + 1)`. -/
theorem two_mul_le_growthConst {p : ℕ} {g N : ℝ} {m' m : ℕ} (hp : 1 ≤ p) (hm : m' ≤ m)
    (hlow : (2 - Real.logb 2 3) * g - 1 < N)
    (hup : N ≤ Real.logb 2 p * (Real.logb 2 3 ^ m' - 1) / (Real.logb 2 3 - 1)) :
    2 * g ≤ growthConst m * (Real.log p + 1) := by
  have h1 := one_lt_logb_two_three
  have h2 := logb_two_three_lt_two
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  have hK : 0 ≤ runConst m := runConst_nonneg m
  have hmono : (Real.logb 2 3 ^ m' - 1) / (Real.logb 2 3 - 1) ≤ runConst m := by
    rw [runConst]
    gcongr; linarith
  have hN : N ≤ Real.log p / Real.log 2 * runConst m := by
    refine hup.trans ?_
    rw [mul_div_assoc, Real.logb]
    exact mul_le_mul_of_nonneg_left hmono (div_nonneg hL hl2.le)
  set k := runConst m / Real.log 2 with hk
  have hk0 : 0 ≤ k := div_nonneg hK hl2.le
  have hkL : Real.log p / Real.log 2 * runConst m = k * Real.log p := by
    rw [hk]; ring
  rw [growthConst, ← hk, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg hk0 hL]

/-- **The bootstrap.** -/
theorem rpow_bootstrap {A M : ℝ} (hA : 1 ≤ A) (hM : 1 ≤ M) :
    ∃ C : ℝ, ∀ p D : ℝ, 1 ≤ p → 1 ≤ D →
      p ≤ M * D * (A * (Real.log p + 1)) ^ (13.3 : ℝ) →
        p ≤ C * D * (Real.log D + 1) ^ (13.3 : ℝ) := by
  set β : ℝ := 13.3 with hβ
  have hβ0 : 0 ≤ β := by norm_num
  set G := (A * (2 * β + 1)) ^ β with hG
  have hG1 : 1 ≤ G := Real.one_le_rpow (by nlinarith) hβ0
  set E := 2 * Real.log M + 2 * Real.log G + 2 with hE
  refine ⟨M * (A * E) ^ β, fun p D hp hD h => ?_⟩
  have hp0 : 0 < p := by linarith
  have hD0 : 0 < D := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlogG : 0 ≤ Real.log G := Real.log_nonneg hG1
  -- `log p + 1 ≤ (2β + 1) q`, `q = p^{1/(2β)}`
  set q := p ^ (1 / (2 * β)) with hq
  have hq1 : 1 ≤ q := Real.one_le_rpow hp (by norm_num)
  have hlq : Real.log p + 1 ≤ (2 * β + 1) * q := by
    have := Real.log_le_rpow_div hp0.le (ε := 1 / (2 * β)) (by norm_num)
    rw [← hq, div_div_eq_mul_div, div_one] at this
    nlinarith
  have hqβ : q ^ β = p ^ (1 / 2 : ℝ) := by
    rw [hq, ← Real.rpow_mul hp0.le]; norm_num
  set s := p ^ (1 / 2 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hp0 _
  have hss : s * s = p := by
    rw [hs, ← Real.rpow_add hp0]; norm_num
  have h1 : (A * (Real.log p + 1)) ^ β ≤ G * s := by
    calc (A * (Real.log p + 1)) ^ β ≤ (A * (2 * β + 1) * q) ^ β := by
          apply Real.rpow_le_rpow (by positivity) _ hβ0
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hlq (by linarith)
      _ = G * s := by rw [Real.mul_rpow (by positivity) (by positivity), hqβ]
  -- `√p ≤ M D G`
  have hsle : s ≤ M * D * G := by
    have : s * s ≤ M * D * G * s := by
      rw [hss]
      calc p ≤ M * D * (A * (Real.log p + 1)) ^ β := h
        _ ≤ M * D * (G * s) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = M * D * G * s := by ring
    nlinarith
  have hpb : p ≤ (M * D * G) ^ 2 := by nlinarith
  have hlogpb : Real.log p ≤ 2 * (Real.log M + Real.log D + Real.log G) := by
    have := Real.log_le_log hp0 hpb
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)] at this
    push_cast at this
    linarith
  have hLD : Real.log p + 1 ≤ E * (Real.log D + 1) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * Real.log M + 2 * Real.log G) hlogD]
  calc p ≤ M * D * (A * (Real.log p + 1)) ^ β := h
    _ ≤ M * D * (A * (E * (Real.log D + 1))) ^ β := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hLD (by linarith)) hβ0
    _ = M * (A * E) ^ β * D * (Real.log D + 1) ^ β := by
        rw [← mul_assoc A E, Real.mul_rpow (by positivity) (by positivity)]
        ring

end CollatzMoonshot.Amusical.NearCycleRuns
