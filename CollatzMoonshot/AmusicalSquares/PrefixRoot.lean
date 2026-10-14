/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# A `3`-adic separation lemma for prefix roots

A sum `Σ_{h ∈ S ∪ {n}} e_h 2^{a_h} / 3^{h+1}` with every `h ∈ S` below `n` and `3 ∤ e_n` is
nonzero: times `3^{n+1}` it is `e_n 2^{a_n}` plus a multiple of `3`.
-/

namespace CollatzMoonshot.Amusical

theorem sum_three_adic_ne_zero (e : ℕ → ℤ) (a : ℕ → ℕ) (S : Finset ℕ) (n : ℕ)
    (hS : ∀ h ∈ S, h < n) (hn : ¬ (3 : ℤ) ∣ e n) :
    (e n : ℚ) * 2 ^ a n / 3 ^ (n + 1) + ∑ h ∈ S, (e h : ℚ) * 2 ^ a h / 3 ^ (h + 1) ≠ 0 := by
  intro hzero
  set M : ℤ := ∑ h ∈ S, e h * 2 ^ a h * 3 ^ (n - h - 1) with hM
  have hterm : ∀ h ∈ S, (e h : ℚ) * 2 ^ a h / 3 ^ (h + 1) * 3 ^ (n + 1) =
      3 * ((e h * 2 ^ a h * 3 ^ (n - h - 1) : ℤ) : ℚ) := by
    intro h hh
    have hlt := hS h hh
    have hexp : n + 1 = (h + 1) + (n - h - 1 + 1) := by omega
    rw [hexp, pow_add, pow_succ]
    push_cast
    field_simp
    ring
  have hkey : ((e n * 2 ^ a n + 3 * M : ℤ) : ℚ) = 0 := by
    have := congrArg (· * (3 : ℚ) ^ (n + 1)) hzero
    simp only [zero_mul, add_mul, Finset.sum_mul] at this
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at this
    rw [hM]
    push_cast at this ⊢
    rw [← this]
    field_simp
  have hint : e n * 2 ^ a n + 3 * M = 0 := by exact_mod_cast hkey
  have h3 : (3 : ℤ) ∣ e n * 2 ^ a n := ⟨-M, by linarith⟩
  have hp : Prime (3 : ℤ) := Int.prime_three
  rcases hp.dvd_or_dvd h3 with h | h
  · exact hn h
  · have := hp.dvd_of_dvd_pow h
    norm_num at this

end CollatzMoonshot.Amusical
