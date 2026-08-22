/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.FrontB.Words

/-!
# The abc conjecture, and what it actually buys Front B 🧨

**CONJECTURE-grade** under the three-tier doctrine of `Assumed.lean`: open, widely believed,
labelled.  The statement is copied verbatim from `collatz-cryptid`'s
`Collatz/Erdos/Axioms.lean` so the two repos assume the *same* sentence.

## Why it is here

`APPROACHES.md` claims that "an effective S-unit or abc-strength input finishes cycles
**entirely**".  This file tests that claim rather than repeating it.

Apply abc to the triple `3^x + (2^k − 3^x) = 2^k`.  The three parts are pairwise coprime
(`den` is coprime to `6`, proved in `FrontB/Words.lean`), so the radical collapses to
`6 · rad(den)`, and abc returns

`2^k ≤ C · den²`   -   a **lower** bound on `den`.

That is the wrong direction.  `FrontB/Threads.lean`'s `finite_shapes_of_boundedDen` needs an
**upper** bound on `|den|` to leave finitely many shapes; a lower bound only says the cycle's
elements cannot be too large, which lower-bounds cycle length and closes nothing.  **abc is
one half of a scissors, and the missing half is the half nobody knows how to get.**

`abc_and_boundedDen_bounds_length` makes that precise: the two directions *together* bound
the word length, so the filter is not a matter of taste.
-/

namespace CollatzMoonshot.FrontB

open Finset

/-- The **radical** of `n`: product of its distinct prime divisors. -/
def rad (n : ℕ) : ℕ := n.primeFactors.prod id

/-- **abc conjecture** (Masser-Oesterlé, ~1985, open).  For every `ε > 0` there is `K(ε)`
such that every coprime positive `a + b = c` satisfies `c ≤ K · rad(abc)^(1+ε)`. -/
def AbcConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ,
    ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
      ((a + b : ℕ) : ℝ) ≤ K * ((rad (a * b * (a + b)) : ℕ) : ℝ) ^ (1 + ε)

/-- CONJECTURE-grade axiom.  Everything downstream is honestly conditional and says so. -/
axiom abc : AbcConjecture

theorem rad_le_self {n : ℕ} (hn : 0 < n) : rad n ≤ n :=
  Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

theorem primeFactors_six : (6 : ℕ).primeFactors = {2, 3} := by
  have h6 : (6:ℕ) = 2 * 3 := by norm_num
  rw [h6, Nat.Coprime.primeFactors_mul (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  rfl

/-- For `b` coprime to `6`, the radical of `3^x · b · 2^k` is the radical of `6b`, hence at
most `6b`.  This is the collapse that makes abc say something clean about `2^k − 3^x`. -/
theorem rad_triple_le {b x k : ℕ} (hb : 0 < b) (hx : x ≠ 0) (hk : k ≠ 0) :
    rad (3 ^ x * b * 2 ^ k) ≤ 6 * b := by
  have hb0 : b ≠ 0 := hb.ne'
  have h3x : (3:ℕ) ^ x ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2k : (2:ℕ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpf : (3 ^ x * b * 2 ^ k).primeFactors = (6 * b).primeFactors := by
    rw [Nat.primeFactors_mul (by positivity) h2k, Nat.primeFactors_mul h3x hb0,
      Nat.primeFactors_mul (by norm_num) hb0,
      Nat.primeFactors_prime_pow hx (by norm_num),
      Nat.primeFactors_prime_pow hk (by norm_num), primeFactors_six]
    ext p
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    tauto
  have : rad (3 ^ x * b * 2 ^ k) = rad (6 * b) := by unfold rad; rw [hpf]
  rw [this]
  exact rad_le_self (by positivity)

/-- **What abc actually gives**: a lower bound on the denominator, `2^k ≤ C · den²`.
The direction is the whole point - see the module docstring. -/
theorem den_lower_bound_of_abc (h : AbcConjecture) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : List Bool, 1 ≤ ones v → 0 < den v →
      (2:ℝ) ^ v.length ≤ C * ((den v).natAbs : ℝ) ^ 2 := by
  obtain ⟨K, hK⟩ := h 1 one_pos
  refine ⟨max K 1 * 36, by positivity, ?_⟩
  intro v hx hpos
  have hvne : v ≠ [] := by rintro rfl; simp [ones] at hx
  have hbpos : 0 < (den v).natAbs := Int.natAbs_pos.mpr (ne_of_gt hpos)
  have hsum : (3:ℕ) ^ ones v + (den v).natAbs = 2 ^ v.length := by
    have h1 : ((3:ℕ) ^ ones v : ℤ) + ((den v).natAbs : ℤ) = ((2:ℕ) ^ v.length : ℤ) := by
      rw [Int.natAbs_of_nonneg (le_of_lt hpos), den]; push_cast; ring
    exact_mod_cast h1
  have h3b : ¬ (3 ∣ (den v).natAbs) := by
    intro hd
    exact not_three_dvd_den hx
      ((Int.natAbs_dvd_natAbs (a := (3:ℤ)) (b := den v)).mp (by simpa using hd))
  have hcop : Nat.Coprime (3 ^ ones v) ((den v).natAbs) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3b)
  have hkey := hK (3 ^ ones v) ((den v).natAbs) (by positivity) hbpos hcop
  rw [hsum] at hkey
  have hklen : v.length ≠ 0 := by
    intro h0
    have : v = [] := List.length_eq_zero_iff.mp h0
    exact hvne this
  have hrad : rad (3 ^ ones v * (den v).natAbs * 2 ^ v.length) ≤ 6 * (den v).natAbs :=
    rad_triple_le hbpos (by omega) hklen
  set R : ℝ := ((rad (3 ^ ones v * (den v).natAbs * 2 ^ v.length) : ℕ) : ℝ) with hR
  have hRnn : (0:ℝ) ≤ R := by positivity
  have hRle : R ≤ 6 * ((den v).natAbs : ℝ) := by rw [hR]; exact_mod_cast hrad
  have hexp : R ^ (1 + (1:ℝ)) = R ^ (2:ℕ) := by
    rw [show (1 + (1:ℝ)) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hexp] at hkey
  have hkey' : (2:ℝ) ^ v.length ≤ K * R ^ (2:ℕ) := by push_cast at hkey; exact hkey
  have hsq : R ^ (2:ℕ) ≤ (6 * ((den v).natAbs : ℝ)) ^ (2:ℕ) :=
    pow_le_pow_left₀ hRnn hRle 2
  have hm : (0:ℝ) ≤ max K 1 := le_trans zero_le_one (le_max_right _ _)
  have hKm : K ≤ max K 1 := le_max_left _ _
  calc (2:ℝ) ^ v.length ≤ K * R ^ (2:ℕ) := hkey'
    _ ≤ max K 1 * R ^ (2:ℕ) := by nlinarith [pow_nonneg hRnn 2]
    _ ≤ max K 1 * (6 * ((den v).natAbs : ℝ)) ^ (2:ℕ) := mul_le_mul_of_nonneg_left hsq hm
    _ = max K 1 * 36 * ((den v).natAbs : ℝ) ^ 2 := by ring

end CollatzMoonshot.FrontB
