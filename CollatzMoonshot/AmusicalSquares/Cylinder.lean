/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical

/-!
# The canonical cylinder of `V = U⁻¹`

One step of `V` is affine on each residue class mod `3`: `V (3M + ρ) = 2^e M + v` with
`e ∈ {1, 2}` and `0 ≤ v < 2^e`.
-/

namespace CollatzMoonshot.Amusical

/-- The exponent of one `V`-step on the class `ρ` mod `3`. -/
def invStepExp (ρ : ℤ) : ℕ := if ρ = 0 then 1 else 2

/-- The offset of one `V`-step on the class `ρ` mod `3`. -/
def invStepOff (ρ : ℤ) : ℤ := if ρ = 0 then 0 else if ρ = 1 then 1 else 3

theorem amusicalInv_three_mul_add (M ρ : ℤ) (h0 : 0 ≤ ρ) (h3 : ρ < 3) :
    amusicalInv (3 * M + ρ) = 2 ^ invStepExp ρ * M + invStepOff ρ := by
  interval_cases ρ <;> simp only [invStepExp, invStepOff] <;> norm_num <;>
    unfold amusicalInv <;> split_ifs <;> omega

theorem invStep_bounds (ρ : ℤ) :
    1 ≤ invStepExp ρ ∧ invStepExp ρ ≤ 2 ∧ 0 ≤ invStepOff ρ ∧
      invStepOff ρ < 2 ^ invStepExp ρ := by
  unfold invStepExp invStepOff; split_ifs <;> norm_num

theorem amusicalInv_iterate_cylinder_aux (k : ℕ) : ∀ r : ℤ, 0 ≤ r → r < 3 ^ k →
    ∃ a : ℕ, ∃ s : ℤ, k ≤ a ∧ a ≤ 2 * k ∧ 0 ≤ s ∧ s < 2 ^ a ∧
      ∀ n : ℤ, amusicalInv^[k] (3 ^ k * n + r) = 2 ^ a * n + s := by
  induction k with
  | zero =>
    intro r hr0 hr
    refine ⟨0, r, le_rfl, by norm_num, hr0, by simpa using hr, fun n => by simp⟩
  | succ k ih =>
    intro r hr0 hr
    have h3k : (0 : ℤ) < 3 ^ k := by positivity
    set q := r / 3 with hq
    set ρ := r % 3 with hρ
    have hrq : r = 3 * q + ρ := by omega
    have hq0 : 0 ≤ q := by omega
    have hqk : q < 3 ^ k := by
      have : r < 3 * 3 ^ k := by rw [pow_succ] at hr; linarith
      omega
    obtain ⟨he1, he2, hv0, hve⟩ := invStep_bounds ρ
    set e := invStepExp ρ with he
    set v := invStepOff ρ with hv
    have h2e : (0 : ℤ) < 2 ^ e := by positivity
    set r' := 2 ^ e * q + v with hr'
    have hr'0 : 0 ≤ r' := by positivity
    have hr'lt : r' < 2 ^ e * 3 ^ k := by nlinarith
    set j := r' / 3 ^ k with hj
    set r'' := r' % 3 ^ k with hr''
    have hj0 : 0 ≤ j := Int.ediv_nonneg hr'0 h3k.le
    have hjlt : j < 2 ^ e := by
      rw [hj]; exact Int.ediv_lt_of_lt_mul h3k (by linarith)
    have hr''0 : 0 ≤ r'' := Int.emod_nonneg _ h3k.ne'
    have hr''lt : r'' < 3 ^ k := Int.emod_lt_of_pos _ h3k
    have hsplit : r' = 3 ^ k * j + r'' := (Int.mul_ediv_add_emod r' (3 ^ k)).symm
    obtain ⟨a, s, hka, ha2k, hs0, hsa, hcyl⟩ := ih r'' hr''0 hr''lt
    have h2a : (0 : ℤ) < 2 ^ a := by positivity
    refine ⟨a + e, 2 ^ a * j + s, by omega, by omega, by positivity, ?_, fun n => ?_⟩
    · rw [pow_add]
      have : j + 1 ≤ 2 ^ e := by omega
      nlinarith
    · have hstep : amusicalInv (3 ^ (k + 1) * n + r) = 3 ^ k * (2 ^ e * n + j) + r'' := by
        have : 3 ^ (k + 1) * n + r = 3 * (3 ^ k * n + q) + ρ := by rw [hrq, pow_succ]; ring
        rw [this, amusicalInv_three_mul_add _ _ (by omega) (by omega), ← he, ← hv]
        linear_combination hsplit
      rw [Function.iterate_succ_apply, hstep, hcyl, pow_add]
      ring

end CollatzMoonshot.Amusical
