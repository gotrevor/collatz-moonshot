/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalSurvivorCeiling

/-!
# Rungs: helpers for the quantized ladder

A rung is a forward survivor `n` with a first backward drop `g`; `p = Vᵍ n`.

* `four_mul_amusical_le_of_odd`: `4 U x ≤ 3x + 1` for odd `x`.
* `iterate_rung`: `Uᵏ p = V^(g−k) n` for `k ≤ g`.
* `rung_fwd`: every forward iterate `Uᵏ p`, `k ≥ 1`, is `≥ n`.
* `rung_base`: `p ≥ 2` and `p` is even; `rung_three_halves`: `2n ≤ 3p`.
* `abs_log_three_add_sub_le`, `log_amusical_step`: one step of the log ledger.
* `rung_log_iter`: the ledger along `p → n`.
-/

namespace CollatzMoonshot.Amusical.NearCycle

theorem four_mul_amusical_le_of_odd {x : ℤ} (hx : Odd x) : 4 * amusical x ≤ 3 * x + 1 := by
  obtain ⟨k, rfl⟩ := hx
  unfold amusical
  split_ifs <;> omega

theorem amusicalInv_nonneg {m : ℤ} (h : 0 ≤ m) : 0 ≤ amusicalInv m := by
  unfold amusicalInv
  split_ifs <;> omega

theorem amusicalInv_iterate_nonneg (t : ℕ) {m : ℤ} (h : 0 ≤ m) : 0 ≤ amusicalInv^[t] m := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact amusicalInv_nonneg ih

theorem iterate_rung {n : ℤ} {g k : ℕ} (hk : k ≤ g) :
    amusical^[k] (amusicalInv^[g] n) = amusicalInv^[g - k] n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show k + j - k = j by omega, Function.iterate_add_apply]
  exact (Function.LeftInverse.iterate amusical_amusicalInv k) _

theorem rung_fwd {n : ℤ} {g : ℕ} (hn : FwdSurvivor n)
    (hmin : ∀ t, 1 ≤ t → t < g → n ≤ amusicalInv^[t] n) :
    ∀ k : ℕ, 1 ≤ k → n ≤ amusical^[k] (amusicalInv^[g] n) := by
  intro k hk
  rcases le_or_gt k g with h | h
  · rw [iterate_rung h]
    rcases Nat.eq_zero_or_pos (g - k) with h0 | h0
    · rw [h0]; simp
    · exact hmin _ h0 (by omega)
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [show g + j + 1 = (j + 1) + g by omega, Function.iterate_add_apply, iterate_rung le_rfl]
    simpa using hn (j + 1) (by omega)

theorem rung_base {n : ℤ} {g : ℕ} (hn : FwdSurvivor n) (hpos : 2 ≤ n)
    (hdrop : amusicalInv^[g] n < n)
    (hmin : ∀ t, 1 ≤ t → t < g → n ≤ amusicalInv^[t] n) :
    2 ≤ amusicalInv^[g] n ∧ amusicalInv^[g] n % 2 = 0 ∧ 2 * n ≤ 3 * amusicalInv^[g] n := by
  have h0 := amusicalInv_iterate_nonneg g (show (0 : ℤ) ≤ n by omega)
  have h1 := rung_fwd hn hmin 1 le_rfl
  simp only [Function.iterate_one] at h1
  generalize amusicalInv^[g] n = p at *
  unfold amusical at h1
  split_ifs at h1 <;> omega

/-- One step of the log ledger: `log (3x + e) − log (3x)` is at most `|e|/(3x − 1)`. -/
theorem abs_log_three_add_sub_le {x e : ℝ} (hx : 1 ≤ x) (he : |e| ≤ 1) :
    |Real.log (3 * x + e) - Real.log (3 * x)| ≤ |e| / (3 * x - 1) := by
  have he1 := neg_abs_le e
  have he2 := le_abs_self e
  have ha : 0 < 3 * x + e := by linarith
  have hb : 0 < 3 * x := by linarith
  have hc : 0 < 3 * x - 1 := by linarith
  rw [abs_le]
  constructor
  · -- `log b − log a ≤ b/a − 1 = −e/a`
    have := Real.log_le_sub_one_of_pos (div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne'] at this
    have h2 : 3 * x / (3 * x + e) - 1 = -e / (3 * x + e) := by field_simp; ring
    have h3 : -e / (3 * x + e) ≤ |e| / (3 * x - 1) := by
      rw [div_le_div_iff₀ ha hc]
      nlinarith [abs_nonneg e]
    linarith
  · have := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [Real.log_div ha.ne' hb.ne'] at this
    have h2 : (3 * x + e) / (3 * x) - 1 = e / (3 * x) := by field_simp; ring
    have h3 : e / (3 * x) ≤ |e| / (3 * x - 1) := by
      rw [div_le_div_iff₀ hb hc]
      nlinarith [abs_nonneg e]
    linarith

/-- One step of `U` in the log ledger: the carry is `0` at even points and `≤ 1/(3m − 1)` at odd
points `x ≥ m`. -/
theorem log_amusical_step {x m : ℤ} (hx : 1 ≤ x) (hm : 1 ≤ m) (h : x % 2 = 0 ∨ m ≤ x) :
    ∃ d : ℕ, |Real.log (amusical x : ℝ) - (Real.log x + Real.log 3 - d * Real.log 2)| ≤
      1 / (3 * (m : ℝ) - 1) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpos : (0 : ℝ) < 3 * m - 1 := by linarith
  obtain ⟨d, e, hd, he, hcarry⟩ : ∃ d : ℕ, ∃ e : ℤ,
      (2 : ℤ) ^ d * amusical x = 3 * x + e ∧ |e| ≤ 1 ∧ (e = 0 ∨ m ≤ x) := by
    unfold amusical
    split_ifs with h1 h2
    · exact ⟨1, 0, by omega, by simp, Or.inl rfl⟩
    · exact ⟨2, 1, by omega, by simp, Or.inr (by omega)⟩
    · exact ⟨2, -1, by omega, by simp, Or.inr (by omega)⟩
  have hd' : (2 : ℝ) ^ d * (amusical x : ℝ) = 3 * x + e := by exact_mod_cast hd
  have he' : |(e : ℝ)| ≤ 1 := by exact_mod_cast he
  have hU : (0 : ℝ) < amusical x := by
    have : (0 : ℝ) < 3 * x + e := by linarith [neg_abs_le (e : ℝ)]
    rw [← hd'] at this
    exact pos_of_mul_pos_right this (by positivity)
  refine ⟨d, ?_⟩
  have hlogU : Real.log (amusical x : ℝ) = Real.log (3 * x + e) - d * Real.log 2 := by
    rw [← hd', Real.log_mul (by positivity) hU.ne', Real.log_pow]
    ring
  have hlog3 : Real.log (3 * (x : ℝ)) = Real.log 3 + Real.log x :=
    Real.log_mul (by norm_num) (by linarith)
  rw [show Real.log (amusical x : ℝ) - (Real.log x + Real.log 3 - d * Real.log 2) =
      Real.log (3 * x + e) - Real.log (3 * x) by rw [hlogU, hlog3]; ring]
  refine (abs_log_three_add_sub_le hx' he').trans ?_
  rcases hcarry with rfl | hmx
  · simp only [Int.cast_zero, abs_zero, zero_div]
    positivity
  · have hmx' : (m : ℝ) ≤ x := by exact_mod_cast hmx
    calc |(e : ℝ)| / (3 * x - 1) ≤ 1 / (3 * x - 1) :=
          div_le_div_of_nonneg_right he' (by linarith)
      _ ≤ 1 / (3 * m - 1) := one_div_le_one_div_of_le hpos (by linarith)

/-- The log ledger along `p → n`. -/
theorem rung_log_iter {n : ℤ} {g : ℕ} (hn : FwdSurvivor n) (hpos : 2 ≤ n)
    (hdrop : amusicalInv^[g] n < n)
    (hmin : ∀ t, 1 ≤ t → t < g → n ≤ amusicalInv^[t] n) :
    ∀ k : ℕ, k ≤ g → ∃ a : ℕ,
      |Real.log (amusical^[k] (amusicalInv^[g] n) : ℝ) -
        (Real.log (amusicalInv^[g] n : ℝ) + k * Real.log 3 - a * Real.log 2)| ≤
        k / (3 * (n : ℝ) - 1) := by
  obtain ⟨hp2, hpe, -⟩ := rung_base hn hpos hdrop hmin
  intro k
  induction k with
  | zero => intro _; exact ⟨0, by simp⟩
  | succ k ih =>
      intro hk
      obtain ⟨a, ha⟩ := ih (by omega)
      set x := amusical^[k] (amusicalInv^[g] n) with hxdef
      have hx : 1 ≤ x ∧ (x % 2 = 0 ∨ n ≤ x) := by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · simp only [Function.iterate_zero, id_eq] at hxdef
          rw [hxdef]; exact ⟨by omega, Or.inl hpe⟩
        · have := rung_fwd hn hmin k hk0
          exact ⟨by omega, Or.inr this⟩
      obtain ⟨d, hd⟩ := log_amusical_step hx.1 (by omega : (1 : ℤ) ≤ n) hx.2
      refine ⟨a + d, ?_⟩
      rw [Function.iterate_succ_apply', ← hxdef]
      have := abs_add_le
        (Real.log (amusical x : ℝ) - (Real.log x + Real.log 3 - d * Real.log 2))
        (Real.log x - (Real.log (amusicalInv^[g] n : ℝ) + k * Real.log 3 - a * Real.log 2))
      have hsplit : (k + 1 : ℕ) / (3 * (n : ℝ) - 1) = 1 / (3 * (n : ℝ) - 1) + k / (3 * n - 1) := by
        push_cast; ring
      rw [hsplit]
      have heq : Real.log (amusical x : ℝ) - (Real.log (amusicalInv^[g] n : ℝ) +
          ((k + 1 : ℕ) : ℝ) * Real.log 3 - ((a + d : ℕ) : ℝ) * Real.log 2) =
          Real.log (amusical x : ℝ) - (Real.log x + Real.log 3 - d * Real.log 2) +
          (Real.log x - (Real.log (amusicalInv^[g] n : ℝ) + k * Real.log 3 - a * Real.log 2)) := by
        push_cast; ring
      rw [heq]
      exact this.trans (add_le_add hd ha)

end CollatzMoonshot.Amusical.NearCycle
