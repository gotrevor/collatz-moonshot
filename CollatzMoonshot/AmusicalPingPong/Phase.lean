/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalAntiKohl

namespace CollatzMoonshot.Amusical

/-- Multiplication by `21/5` preserves the six residues in the A phase. -/
theorem phaseK_step {x y : ℤ} (hx : x % 19 ∈ ({1, 7, 8, 11, 12, 18} : Finset ℤ))
    (hxy : 5 * y = 21 * x) : y % 19 ∈ ({1, 7, 8, 11, 12, 18} : Finset ℤ) := by
  have hy : y % 19 = (8 * (x % 19)) % 19 := by omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with hx | hx | hx | hx | hx | hx <;> simp [hy, hx]

/-- An A-phase point of residue `1` enters the B phase after multiplication by `15`. -/
theorem phaseAB_step {x : ℤ} (hx : x % 19 = 1) :
    (15 * x) % 19 ∈ ({4, 6, 9, 10, 13, 15} : Finset ℤ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Multiplication by `75/7` preserves the six residues in the B phase. -/
theorem phaseB_step {x y : ℤ} (hx : x % 19 ∈ ({4, 6, 9, 10, 13, 15} : Finset ℤ))
    (hxy : 7 * y = 75 * x) : y % 19 ∈ ({4, 6, 9, 10, 13, 15} : Finset ℤ) := by
  have hy : y % 19 = (8 * (x % 19)) % 19 := by omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with hx | hx | hx | hx | hx | hx <;> simp [hy, hx]

/-- Every power of `8` modulo `19` lies in the six-element A phase. -/
theorem pow_eight_emod_mem_phaseK (n : ℕ) :
    (8 : ℤ) ^ n % 19 ∈ ({1, 7, 8, 11, 12, 18} : Finset ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      simp only [Finset.mem_insert, Finset.mem_singleton] at ih ⊢
      rcases ih with ih | ih | ih | ih | ih | ih <;> simp [Int.mul_emod, ih]

/-- A residue whose product with a power of `8` is `1` lies in the A phase. -/
theorem phaseK_of_mul_pow_eight_emod_eq_one {x : ℤ} {a : ℕ}
    (hx : (x * 8 ^ a) % 19 = 1) :
    x % 19 ∈ ({1, 7, 8, 11, 12, 18} : Finset ℤ) := by
  have hp := pow_eight_emod_mem_phaseK a
  have hm : ((x % 19) * (8 ^ a % 19)) % 19 = 1 := by
    rw [Int.mul_emod] at hx
    exact hx
  have hx0 : 0 ≤ x % 19 := Int.emod_nonneg _ (by norm_num)
  have hx19 : x % 19 < 19 := Int.emod_lt_of_pos _ (by norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
  rcases hp with hp | hp | hp | hp | hp | hp <;> rw [hp] at hm <;> omega

/-- Both counter transitions multiply the phase by `8` modulo `19`.

The countdown formulation is convenient for a run with `a + 1` steps left. -/
theorem phase_countdown_step {x y : ℤ} {a : ℕ}
    (hxy : 5 * y = 21 * x ∨ 7 * y = 75 * x) {r : ℤ}
    (hx : (x * 8 ^ (a + 1)) % 19 = r % 19) :
    (y * 8 ^ a) % 19 = r % 19 := by
  have hy : y ≡ 8 * x [ZMOD 19] := by
    rcases hxy with hxy | hxy <;> change y % 19 = (8 * x) % 19 <;> omega
  calc
    (y * 8 ^ a) % 19 = ((8 * x) * 8 ^ a) % 19 := (hy.mul_right _).eq
    _ = (x * 8 ^ (a + 1)) % 19 := by
      congr 1
      rw [pow_succ]
      ring
    _ = r % 19 := hx

/-- Every engine transition has an output divisible by three. -/
theorem three_dvd_of_engine_equation {x y : ℤ}
    (hxy : 5 * y = 21 * x ∨ y = 15 * x ∨ 7 * y = 75 * x ∨ y = 3 * x) :
    y % 3 = 0 := by
  rcases hxy with hxy | hxy | hxy | hxy <;> omega

/-- The A transition lowers the 5-adic counter and raises the 7-adic counter. -/
theorem valuation_stepA {x y : ℤ} (hx : x ≠ 0) (hxy : 5 * y = 21 * x) :
    y ≠ 0 ∧ padicValInt 5 x = padicValInt 5 y + 1 ∧
      padicValInt 7 y = padicValInt 7 x + 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hy : y ≠ 0 := by
    intro hy
    rw [hy] at hxy
    simp at hxy
    exact hx (by omega)
  refine ⟨hy, ?_, ?_⟩
  · have hv := congrArg (padicValInt 5) hxy
    rw [padicValInt.mul (by norm_num) hy, padicValInt.mul (by norm_num) hx] at hv
    have h5 : padicValInt 5 (5 : ℤ) = 1 := padicValInt.self (by norm_num)
    have h21 : padicValInt 5 (21 : ℤ) = 0 :=
      padicValInt.eq_zero_of_not_dvd (by norm_num)
    rw [h5, h21] at hv
    omega
  · have hv := congrArg (padicValInt 7) hxy
    rw [padicValInt.mul (by norm_num) hy, padicValInt.mul (by norm_num) hx] at hv
    have h5 : padicValInt 7 (5 : ℤ) = 0 :=
      padicValInt.eq_zero_of_not_dvd (by norm_num)
    have h21 : padicValInt 7 (21 : ℤ) = 1 := by
      rw [show (21 : ℤ) = 3 * 7 by norm_num, padicValInt.mul (by norm_num) (by norm_num)]
      have hs : padicValInt 7 (7 : ℤ) = 1 := padicValInt.self (p := 7) (by norm_num)
      rw [padicValInt.eq_zero_of_not_dvd (by norm_num), hs]
    rw [h5, h21] at hv
    omega

/-- The B transition lowers the 7-adic counter and raises the 5-adic counter by two. -/
theorem valuation_stepB {x y : ℤ} (hx : x ≠ 0) (hxy : 7 * y = 75 * x) :
    y ≠ 0 ∧ padicValInt 7 x = padicValInt 7 y + 1 ∧
      padicValInt 5 y = padicValInt 5 x + 2 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hy : y ≠ 0 := by
    intro hy
    rw [hy] at hxy
    simp at hxy
    exact hx (by omega)
  refine ⟨hy, ?_, ?_⟩
  · have hv := congrArg (padicValInt 7) hxy
    rw [padicValInt.mul (by norm_num) hy, padicValInt.mul (by norm_num) hx] at hv
    have h7 : padicValInt 7 (7 : ℤ) = 1 := padicValInt.self (by norm_num)
    have h75 : padicValInt 7 (75 : ℤ) = 0 :=
      padicValInt.eq_zero_of_not_dvd (by norm_num)
    rw [h7, h75] at hv
    omega
  · have hv := congrArg (padicValInt 5) hxy
    rw [padicValInt.mul (by norm_num) hy, padicValInt.mul (by norm_num) hx] at hv
    have h7 : padicValInt 5 (7 : ℤ) = 0 :=
      padicValInt.eq_zero_of_not_dvd (by norm_num)
    have h75 : padicValInt 5 (75 : ℤ) = 2 := by
      rw [show (75 : ℤ) = 3 * 5 * 5 by norm_num, padicValInt.mul (by norm_num) (by norm_num),
        padicValInt.mul (by norm_num) (by norm_num)]
      have hs : padicValInt 5 (5 : ℤ) = 1 := padicValInt.self (p := 5) (by norm_num)
      rw [padicValInt.eq_zero_of_not_dvd (by norm_num), hs]
    rw [h7, h75] at hv
    omega

/-- For a nonzero integer, positive `p`-adic valuation detects divisibility by `p`. -/
theorem emod_eq_zero_iff_padicValInt_pos {p : ℕ} [Fact p.Prime] {x : ℤ} (hx : x ≠ 0) :
    x % p = 0 ↔ 0 < padicValInt p x := by
  rw [← Int.dvd_iff_emod_eq_zero, ← pow_one (p : ℤ), padicValInt_dvd_iff]
  simp [hx, Nat.lt_iff_add_one_le]

end CollatzMoonshot.Amusical
