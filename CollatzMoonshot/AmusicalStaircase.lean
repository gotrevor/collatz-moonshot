/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalSurvivorSeparation

/-!
# Staircases: powers of `2` climb to powers of `3`

`U(2y) = 3y` exactly, so the orbit of `3^s y` contains the ratio-`3/2` staircase
`2^(s−b) 3^b y`, `0 ≤ b ≤ s`, climbed by `s` exact `E`-steps.  The 2026-10-14 "lfsep" agent used it
to feed the survivor separation lemma (`fwdSurvivor_three_separation`).

**`staircase_fwdSurvivor` (Lemma St).**  A staircase point lying at or below the whole forward orbit
of the top `3^(a+b) y` is a forward survivor.

**Theorem P3 (agent; research §30).**  With `X = 2^L y`, the orbits of `3^s y` for `s < L` whose
forward minimum is at least `3X/2` are pairwise distinct and infinite: each staircase has a point
in `3ℤ ∩ [X, 3X/2)`, which survives, and Sep3 separates them.  So if `U` had only `r` infinite
orbits, all but `O(r log S)` of the `s ≤ S` would "fall back": the orbit of `2^s`, after climbing to
`3^s`, would return below `3 · 2^((1+η)s)`.  Measured for `s ≤ 3000` (`η = 0.01`), only
`s = 4, 5, 6, 7, 10` fall back.  But each surviving `s` already exhibits an infinite orbit, which is
Conway's open question, so the logarithmic count is no easier than one.
-/

namespace CollatzMoonshot.Amusical

/-- The staircase: `j ≤ a` exact `E`-steps take `2^a 3^b y` to `2^(a−j) 3^(b+j) y`. -/
theorem amusical_iterate_staircase (y : ℤ) (a b j : ℕ) (hj : j ≤ a) :
    amusical^[j] (2 ^ a * 3 ^ b * y) = 2 ^ (a - j) * 3 ^ (b + j) * y := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, a - j = k + 1 := ⟨a - j - 1, by omega⟩
      rw [hk, show a - (j + 1) = k by omega, pow_succ,
        show (2 : ℤ) ^ k * 2 * 3 ^ (b + j) * y = 2 * (2 ^ k * 3 ^ (b + j) * y) by ring,
        amusical_two_mul, show b + (j + 1) = (b + j) + 1 by omega, pow_succ]
      ring

/-- **Proved (Lemma St).**  A staircase point at or below the forward orbit of its top is a
forward survivor. -/
theorem staircase_fwdSurvivor {y : ℤ} (hy : 0 < y) (a b : ℕ)
    (htop : ∀ t : ℕ, 2 ^ a * 3 ^ b * y ≤ amusical^[t] (3 ^ (a + b) * y)) :
    FwdSurvivor (2 ^ a * 3 ^ b * y) := by
  intro t ht
  rcases le_or_gt t a with hta | hta
  · rw [amusical_iterate_staircase y a b t hta]
    have h2 : (2 : ℤ) ^ a = 2 ^ (a - t) * 2 ^ t := by rw [← pow_add]; congr 1; omega
    have h23 : (2 : ℤ) ^ t ≤ 3 ^ t := pow_le_pow_left₀ (by norm_num) (by norm_num) t
    rw [h2, pow_add]
    have : (0 : ℤ) < 2 ^ (a - t) * 3 ^ b * y := by positivity
    nlinarith
  · obtain ⟨u, rfl⟩ : ∃ u, t = u + a := ⟨t - a, by omega⟩
    rw [Function.iterate_add_apply, amusical_iterate_staircase y a b a le_rfl, Nat.sub_self,
      pow_zero, one_mul, add_comm b a]
    exact htop u

end CollatzMoonshot.Amusical
