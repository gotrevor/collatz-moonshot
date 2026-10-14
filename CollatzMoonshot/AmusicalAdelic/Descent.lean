/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The `2`-adic descent behind Proposition L

Generic in the map `f : ℚ → ℚ`: if `f x = 3x/2` whenever `x` has odd denominator and even
numerator, and `4 f x - 3 x = ±1` whenever `x` is a `2`-adic unit, then every nonzero subgroup of
`ℤ_(2)` closed under `f` contains `1`.  `AmusicalAdelic.lean` instantiates `f = amusicalRat`.
-/

namespace CollatzMoonshot.Amusical.Adelic

/-- Cross-multiplied form of `x = a / d`. -/
lemma num_mul_eq (x : ℚ) (a d : ℤ) (hd : (d : ℚ) ≠ 0) (hx : x = a / d) :
    x.num * d = a * x.den := by
  have h1 : (x.num : ℚ) = x * x.den := (Rat.mul_den_eq_num x).symm
  have h2 : ((x.num * d : ℤ) : ℚ) = ((a * x.den : ℤ) : ℚ) := by
    push_cast; rw [h1, hx]; field_simp
  exact_mod_cast h2

variable (f : ℚ → ℚ)
  (hhalf : ∀ x : ℚ, x.den % 2 = 1 → (x.num * x.den) % 2 = 0 → f x = 3 * x / 2)
  (hunit : ∀ x : ℚ, x.den % 2 = 1 → (x.num * x.den) % 2 = 1 →
    4 * f x - 3 * x = 1 ∨ 4 * f x - 3 * x = -1)
include hhalf hunit

/-- Descent on the `2`-adic valuation of the numerator: if `a / d ∈ Λ` (`d` odd) and
`2 ^ n ∤ a`, then `1 ∈ Λ`. -/
lemma one_mem_of_not_dvd (Λ : AddSubgroup ℚ) (hden : ∀ x ∈ Λ, x.den % 2 = 1)
    (hinv : ∀ x ∈ Λ, f x ∈ Λ) (d : ℤ) (hd : d % 2 = 1) :
    ∀ n : ℕ, ∀ a : ℤ, ¬ (2 : ℤ) ^ n ∣ a → (a / d : ℚ) ∈ Λ → (1 : ℚ) ∈ Λ := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  intro n
  induction n with
  | zero => intro a ha; simp at ha
  | succ n ih =>
    intro a ha hmem
    set x : ℚ := a / d with hxdef
    have hxd := hden x hmem
    have hcross := num_mul_eq x a d hd0 rfl
    rcases Int.emod_two_eq_zero_or_one a with hae | hao
    · -- `a` even: `f x = 3x/2 = (3(a/2))/d`, one fewer factor of `2`.
      obtain ⟨c, rfl⟩ : ∃ c, a = 2 * c := ⟨a / 2, by omega⟩
      have hnum : (x.num * x.den) % 2 = 0 := by
        have : Even (x.num * d) := by rw [hcross]; exact (even_two_mul c).mul_right _
        rcases Int.even_mul.mp this with h | h
        · exact Int.even_iff.mp (h.mul_right _)
        · exact absurd h (by rw [Int.not_even_iff]; exact hd)
      have hU : f x = ((3 * c : ℤ) : ℚ) / d := by
        rw [hhalf x hxd hnum, hxdef]; push_cast; ring
      refine ih (3 * c) ?_ (hU ▸ hinv x hmem)
      intro h3
      apply ha
      have hcop : IsCoprime ((2 : ℤ) ^ n) 3 :=
        IsCoprime.pow_left ⟨-1, 1, by norm_num⟩
      rw [pow_succ, mul_comm _ 2]
      exact mul_dvd_mul_left 2 (hcop.dvd_of_dvd_mul_left h3)
    · -- `a` odd: `x` is a `2`-adic unit, and `4 f x - 3 x = ±1 ∈ Λ`.
      have hodd : Odd (a * x.den) :=
        Int.odd_iff.mpr hao |>.mul (Int.odd_iff.mpr (by exact_mod_cast hxd))
      rw [← hcross] at hodd
      have hxo : (x.num * x.den) % 2 = 1 :=
        Int.odd_iff.mp (Int.odd_mul.mpr ⟨(Int.odd_mul.mp hodd).1,
          Int.odd_iff.mpr (by exact_mod_cast hxd)⟩)
      have hm : (4 : ℕ) • f x - (3 : ℕ) • x ∈ Λ :=
        sub_mem (AddSubgroup.nsmul_mem _ (hinv x hmem) _) (AddSubgroup.nsmul_mem _ hmem _)
      simp only [nsmul_eq_mul, Nat.cast_ofNat] at hm
      rcases hunit x hxd hxo with h | h
      · rwa [h] at hm
      · rw [h] at hm; simpa using neg_mem hm

/-- **Proposition L, generic form.**  A nonzero subgroup of `ℤ_(2)` closed under `f`
contains `1`. -/
theorem one_mem (Λ : AddSubgroup ℚ) (hden : ∀ x ∈ Λ, x.den % 2 = 1)
    (hinv : ∀ x ∈ Λ, f x ∈ Λ) (hne : Λ ≠ ⊥) : (1 : ℚ) ∈ Λ := by
  obtain ⟨⟨x, hx⟩, hx0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hne
  have hx0' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hd : (x.den : ℤ) % 2 = 1 := by exact_mod_cast hden x hx
  refine one_mem_of_not_dvd f hhalf hunit Λ hden hinv x.den hd x.num.natAbs x.num ?_ ?_
  · intro h
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hx0'))
      (by simpa [Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr h)
    exact absurd hle (not_le.mpr Nat.lt_two_pow_self)
  · rw [Int.cast_natCast, Rat.num_div_den]; exact hx

end CollatzMoonshot.Amusical.Adelic
