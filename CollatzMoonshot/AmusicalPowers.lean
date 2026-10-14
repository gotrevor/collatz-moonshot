/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalStaircase

/-!
# Powers of `3`: staircases in one window separate orbits (Theorem P3)

The 2026-10-14 "lfsep" agent's Theorem P3 and Corollary P3′ (research §30).  Fix `y > 0` prime to
`6` and put `X = 2^L y`.  For `s < L` the orbit of `3^s y` contains the ratio-`3/2` staircase
`2^(s−b) 3^b y`, `0 ≤ b ≤ s` (`amusical_iterate_staircase`).  Its lowest point divisible by `3`
(`b = 1`) is `3 · 2^(s−1) y ≤ 3X/4`.  If the whole forward orbit of `3^s y` stays at or above
`3X/2`, the staircase has a point `n_s ∈ 3ℤ ∩ [X, 3X/2)`, which is a forward survivor by Lemma St
(`staircase_fwdSurvivor`).

**`powers_orbit_ne` (P3).**  Two such `s ≠ s'` lie on distinct orbits: `n_s ≠ n_s'` by unique
factorization (`y` prime to `6`), and Sep3 (`fwdSurvivor_three_not_mem_orbit`) separates forward
survivors divisible by `3` in one window.  Each such orbit is infinite
(`powers_not_periodic`, from `fwdSurvivor_three_not_periodic`).

**`infinitelyManyOrbits_of_powers` (P3, counting form).**  If for every `r` some `L` has more than
`r` such exponents, `U` has infinitely many orbits on `ℕ`.

**`infinitelyManyOrbits_of_powers_log` (P3′).**  With `η = 1/k`: if the exponents `s ≤ S` whose
orbit never returns below `3 · 2^(s + s/k + 1) y / 2` are not `O(log S)`, `U` has infinitely many
orbits.  Paper proof: cover `[1, S]` by `O(k log S)` blocks `[L_j, L_{j+1})` with
`L_{j+1} = L_j + L_j / (k + 1) + 1`; every exponent of a block is admissible for `L = L_{j+1}`, so
each block holds at most `r` of them.

This is a reduction, not progress on the count: one admissible `s` already exhibits an infinite
orbit, which is Conway's open question (§30).  Measured for `y = 1`, `s ≤ 3000`, `η = 0.01`: only
`s = 4, 5, 6, 7, 10` fail.
-/

namespace CollatzMoonshot.Amusical

/-- `s` is admissible for the window `[2^L y, 3 · 2^L y / 2)`: `s < L` and the forward orbit of
`3^s y` never drops below `3 · 2^L y / 2`. -/
def PowerAdmissible (y : ℤ) (L s : ℕ) : Prop :=
  s < L ∧ ∀ t : ℕ, 3 * (2 ^ L * y) ≤ 2 * amusical^[t] (3 ^ s * y)

/-- **Target.**  An admissible staircase has a point divisible by `3` in `[2^L y, 3 · 2^L y / 2)`
(`1 ≤ b ≤ s`; such a point is a forward survivor by `staircase_fwdSurvivor`). -/
theorem powerAdmissible_window_point {y : ℤ} (hy : 0 < y) {L s : ℕ}
    (h : PowerAdmissible y L s) :
    ∃ b : ℕ, 1 ≤ b ∧ b ≤ s ∧ 2 ^ L * y ≤ 2 ^ (s - b) * 3 ^ b * y ∧
      2 * (2 ^ (s - b) * 3 ^ b * y) < 3 * (2 ^ L * y) := by
  sorry

/-- **Target (P3).**  Distinct admissible exponents give distinct orbits. -/
theorem powers_orbit_ne {y : ℤ} (hy : 0 < y) (hy2 : ¬ 2 ∣ y) (hy3 : ¬ 3 ∣ y) {L s s' : ℕ}
    (hs : PowerAdmissible y L s) (hs' : PowerAdmissible y L s') (hne : s ≠ s') :
    3 ^ s' * y ∉ amusicalOrbit (3 ^ s * y) := by
  sorry

/-- **Target.**  An admissible power lies on an infinite orbit. -/
theorem powers_not_periodic {y : ℤ} (hy : 0 < y) {L s : ℕ} (hs : PowerAdmissible y L s) :
    3 ^ s * y ∉ Function.periodicPts amusical := by
  sorry

/-- **Target (P3, counting form).**  Unboundedly many admissible exponents for single windows
imply Klamkin (a). -/
theorem infinitelyManyOrbits_of_powers {y : ℤ} (hy : 0 < y) (hy2 : ¬ 2 ∣ y) (hy3 : ¬ 3 ∣ y)
    (h : ∀ r : ℕ, ∃ L : ℕ, ∃ T : Finset ℕ, r < T.card ∧ ∀ s ∈ T, PowerAdmissible y L s) :
    AmusicalInfinitelyManyOrbits := by
  sorry

/-- **Target (P3′).**  With `η = 1/k`: if the exponents `s ≤ S` whose orbit stays at or above
`3 · 2^(s + s/k + 1) y / 2` are not `O(log S)`, `U` has infinitely many orbits on `ℕ`. -/
theorem infinitelyManyOrbits_of_powers_log {y : ℤ} (hy : 0 < y) (hy2 : ¬ 2 ∣ y)
    (hy3 : ¬ 3 ∣ y) (k : ℕ) (hk : 0 < k)
    (h : ∀ C : ℕ, ∃ S : ℕ, ∃ T : Finset ℕ, C * (Nat.log 2 S + 1) < T.card ∧
      ∀ s ∈ T, s ≤ S ∧ PowerAdmissible y (s + s / k + 1) s) :
    AmusicalInfinitelyManyOrbits := by
  sorry

end CollatzMoonshot.Amusical
