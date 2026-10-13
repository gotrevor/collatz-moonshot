/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical

/-!
# Chain connectivity: what one chain can and cannot carry

From the 2026-10-13 "chains" research agent (research note §7).  Treadmill target
(`KICKOFF-2026-10-13-amusical-chains.md`): close every `sorry` here.

* Window minima are spread out along an orbit (`IsWindowMin.iterate_eq_of_isWindowMin`).
* The window densities are uniformly positive: `fwdSurv L ≥ 1/6`, `bwdSurv L ≥ 1/6`, by the
  induction `g_L(s) ≥ 1 − e^{-s}` that uses only the Haar balance `E[e^{-X}] = 1`.
* Together with `windowMinDensity`, finitely many orbits would force an infinite orbit with
  `liminf |U^j x| / |j| = 0`: the **sublinear** recurrence, sharper than
  `exists_linearlyRecurrent_of_finitelyManyOrbits`.
* `AmusicalAtLeastSevenOrbits ∨ (amusicalOrbit 8).Infinite`.
-/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- **Target.**  Two `L`-window minima at most `L` steps apart on one orbit coincide:
`n ≤ U^t n` and `U^t n ≤ U^-t (U^t n) = n`. -/
theorem IsWindowMin.iterate_eq_of_isWindowMin {L t : ℕ} {n : ℤ} (h : IsWindowMin L n)
    (ht : 0 < t) (htL : t ≤ L) (h' : IsWindowMin L (amusical^[t] n)) : amusical^[t] n = n := by
  apply le_antisymm
  · have hback := (h' t ht htL).2
    rw [amusicalInv_iterate_eq_perm_pow, amusical_iterate_eq_perm_pow] at hback
    have hback' : (amusicalPerm ^ (t : ℤ)) n ≤ n := by
      simpa [← Equiv.Perm.mul_apply] using hback
    rwa [amusical_iterate_eq_perm_pow]
  · exact (h t ht htL).1

/-- **Target.**  The forward survival probability is at least `1/6` for every `L`. -/
theorem fwdSurv_ge (L : ℕ) : 1 / 6 ≤ fwdSurv L := by
  sorry

/-- **Target.**  The backward survival probability is at least `1/6` for every `L`. -/
theorem bwdSurv_ge (L : ℕ) : 1 / 6 ≤ bwdSurv L := by
  sorry

/-- Window minima have density at least `1/36` for every window length. -/
theorem windowDensity_ge (L : ℕ) : 1 / 36 ≤ fwdSurv L * bwdSurv L := by
  have h1 := fwdSurv_ge L
  have h2 := bwdSurv_ge L
  calc (1 : ℚ) / 36 = 1 / 6 * (1 / 6) := by norm_num
    _ ≤ fwdSurv L * bwdSurv L := mul_le_mul h1 h2 (by norm_num) (by linarith)

/-- **Target.**  The sublinear recurrence: finitely many orbits would force some infinite orbit
to come back below `|j|/C` at arbitrarily late times, for every `C`.  Paper proof: at least
`δ_L X − o(X) ≥ X/37` window minima lie below `X`; on one chain their times are more than `L`
apart, so `k` chains span time `≥ L X/37 − O(k)`; one chain has `|j| ≥ L X/(75k)` with value
`< X`; let `L → ∞` and pigeonhole over the finitely many chains. -/
theorem exists_sublinearlyRecurrent_of_finitelyManyOrbits (h : ¬ AmusicalInfinitelyManyOrbits) :
    ∃ x : ℤ, 0 ≤ x ∧ (amusicalOrbit x).Infinite ∧ ∀ C : ℝ, 0 < C → ∀ J : ℕ,
      ∃ j : ℤ, (J : ℤ) ≤ |j| ∧ C * (((amusicalPerm ^ j) x : ℤ) : ℝ) ≤ |(j : ℝ)| := by
  sorry

/-- **Target.**  A seventh orbit, or the orbit of `8` is infinite: if the orbit of `8` were a
cycle, the least integer outside it and the five known cycles would start a seventh orbit. -/
theorem atLeastSeven_or_orbitEight_infinite :
    AmusicalAtLeastSevenOrbits ∨ (amusicalOrbit 8).Infinite := by
  sorry

/-- **Reopen condition (weaker than `NoLinearRecurrence`).**  Every aperiodic orbit grows at
least linearly in time: `|U^j x| ≥ c |j|` for all large `|j|`. -/
def AtLeastLinearGrowth : Prop :=
  ∀ x : ℤ, 0 ≤ x → (amusicalOrbit x).Infinite → ∃ c : ℝ, 0 < c ∧ ∃ J : ℕ, ∀ j : ℤ,
    (J : ℤ) ≤ |j| → c * |(j : ℝ)| ≤ (((amusicalPerm ^ j) x : ℤ) : ℝ)

/-- At-least-linear growth of every aperiodic orbit settles Klamkin's problem (a). -/
theorem amusicalInfinitelyManyOrbits_of_atLeastLinearGrowth (hg : AtLeastLinearGrowth) :
    AmusicalInfinitelyManyOrbits := by
  by_contra hfin
  obtain ⟨x, hx0, hinf, hrec⟩ := exists_sublinearlyRecurrent_of_finitelyManyOrbits hfin
  obtain ⟨c, hc, J, hJ⟩ := hg x hx0 hinf
  obtain ⟨j, hjJ, hj⟩ := hrec (2 / c) (by positivity) (J + 1)
  have h1 := hJ j (by omega)
  have hjpos : (0 : ℝ) < |(j : ℝ)| := by
    have : (1 : ℤ) ≤ |j| := by omega
    exact_mod_cast lt_of_lt_of_le one_pos this
  have : 2 / c * (c * |(j : ℝ)|) ≤ |(j : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) hj
  rw [← mul_assoc, div_mul_cancel₀ 2 hc.ne'] at this
  linarith

end CollatzMoonshot.Amusical
