/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical
import CollatzMoonshot.AmusicalBound

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

/-! The survival estimates are most transparent with the current multiplicative
height retained as a rational number `a / b`.  These recursors are the finite
horizon walks before translating back to the word sums `fwdSurv` and
`bwdSurv`. -/

def fwdWalk : ℕ → ℕ → ℕ → ℚ
  | 0, _, _ => 1
  | L + 1, a, b =>
      (if 2 * a < 3 * b then (1 / 2 : ℚ) * fwdWalk L (2 * a) (3 * b) else 0) +
      (if 4 * a < 3 * b then (1 / 2 : ℚ) * fwdWalk L (4 * a) (3 * b) else 0)

def bwdWalk : ℕ → ℕ → ℕ → ℚ
  | 0, _, _ => 1
  | L + 1, a, b =>
      (if 3 * a < 2 * b then (1 / 3 : ℚ) * bwdWalk L (3 * a) (2 * b) else 0) +
      (if 3 * a < 4 * b then (2 / 3 : ℚ) * bwdWalk L (3 * a) (4 * b) else 0)

theorem fwdWalk_ge (L a b : ℕ) (ha : 0 < a) (hab : a < b) :
    1 - (a : ℚ) / b ≤ fwdWalk L a b := by
  induction L generalizing a b with
  | zero => simp [fwdWalk, div_nonneg]
  | succ L ih =>
      have hb : 0 < b := lt_trans ha hab
      have h2 : 2 * a < 3 * b := by omega
      rw [fwdWalk, if_pos h2]
      by_cases h4 : 4 * a < 3 * b
      · rw [if_pos h4]
        have hpos2 : 0 < 2 * a := by positivity
        have hpos4 : 0 < 4 * a := by positivity
        have hleft := ih (2 * a) (3 * b) hpos2 h2
        have hright := ih (4 * a) (3 * b) hpos4 h4
        norm_num [Nat.cast_mul] at hleft hright
        have hbq : (0 : ℚ) < b := by exact_mod_cast hb
        calc
          1 - (a : ℚ) / b =
              (1 / 2 : ℚ) * (1 - (2 * a : ℕ) / (3 * b)) +
                (1 / 2 : ℚ) * (1 - (4 * a : ℕ) / (3 * b)) := by
                  norm_num [Nat.cast_mul]
                  field_simp
                  ring
          _ ≤ (1 / 2 : ℚ) * fwdWalk L (2 * a) (3 * b) +
                (1 / 2 : ℚ) * fwdWalk L (4 * a) (3 * b) := by
                  gcongr
                  · simpa [Nat.cast_mul] using ih (2 * a) (3 * b) hpos2 h2
                  · simpa [Nat.cast_mul] using ih (4 * a) (3 * b) hpos4 h4
      · rw [if_neg h4]
        have hleft := ih (2 * a) (3 * b) (by positivity) h2
        norm_num [Nat.cast_mul] at hleft
        have hbq : (0 : ℚ) < b := by exact_mod_cast hb
        have h4' : 3 * b ≤ 4 * a := by omega
        calc
          1 - (a : ℚ) / b ≤ (1 / 2 : ℚ) * (1 - (2 * a : ℕ) / (3 * b)) := by
            have h4q : (3 : ℚ) * b ≤ 4 * a := by exact_mod_cast h4'
            push_cast
            field_simp
            linarith
          _ ≤ (1 / 2 : ℚ) * fwdWalk L (2 * a) (3 * b) := by
            gcongr
            simpa [Nat.cast_mul] using ih (2 * a) (3 * b) (by positivity) h2
          _ = _ := by ring

theorem bwdWalk_ge (L a b : ℕ) (ha : 0 < a) (hab : a < b) :
    1 - (a : ℚ) / b ≤ bwdWalk L a b := by
  induction L generalizing a b with
  | zero => simp [bwdWalk, div_nonneg]
  | succ L ih =>
      have hb : 0 < b := lt_trans ha hab
      have h4 : 3 * a < 4 * b := by omega
      rw [bwdWalk, if_pos h4]
      by_cases h2 : 3 * a < 2 * b
      · rw [if_pos h2]
        have hleft := ih (3 * a) (2 * b) (by positivity) h2
        have hright := ih (3 * a) (4 * b) (by positivity) h4
        norm_num [Nat.cast_mul] at hleft hright
        have hbq : (0 : ℚ) < b := by exact_mod_cast hb
        calc
          1 - (a : ℚ) / b =
              (1 / 3 : ℚ) * (1 - (3 * a : ℕ) / (2 * b)) +
                (2 / 3 : ℚ) * (1 - (3 * a : ℕ) / (4 * b)) := by
                  norm_num [Nat.cast_mul]
                  field_simp
                  ring
          _ ≤ (1 / 3 : ℚ) * bwdWalk L (3 * a) (2 * b) +
                (2 / 3 : ℚ) * bwdWalk L (3 * a) (4 * b) := by
                  gcongr
                  · simpa [Nat.cast_mul] using ih (3 * a) (2 * b) (by positivity) h2
                  · simpa [Nat.cast_mul] using ih (3 * a) (4 * b) (by positivity) h4
      · rw [if_neg h2]
        have hright := ih (3 * a) (4 * b) (by positivity) h4
        norm_num [Nat.cast_mul] at hright
        have hbq : (0 : ℚ) < b := by exact_mod_cast hb
        have h2' : 2 * b ≤ 3 * a := by omega
        calc
          1 - (a : ℚ) / b ≤ (2 / 3 : ℚ) * (1 - (3 * a : ℕ) / (4 * b)) := by
            have h2q : (2 : ℚ) * b ≤ 3 * a := by exact_mod_cast h2'
            push_cast
            field_simp
            linarith
          _ ≤ (2 / 3 : ℚ) * bwdWalk L (3 * a) (4 * b) := by
            gcongr
            simpa [Nat.cast_mul] using ih (3 * a) (4 * b) (by positivity) h4
          _ = _ := by ring

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
  by_cases h8 : (amusicalOrbit 8).Infinite
  · exact Or.inr h8
  left
  have hknown : (knownCycleMembers : Set ℤ).Finite := Finset.finite_toSet _
  have hfinite : ((knownCycleMembers : Set ℤ) ∪ amusicalOrbit 8).Finite :=
    hknown.union (Set.not_infinite.1 h8)
  obtain ⟨n, hn0, hn⟩ :=
    (Set.Ici_infinite (0 : ℤ)).sdiff hfinite |>.nonempty
  have hclosed : ∀ a ∈ ({0, 1, 2, 4, 44} : Finset ℤ),
      amusicalOrbit a ⊆ (knownCycleMembers : Set ℤ) := by
    intro a ha
    apply amusicalOrbit_subset_of_closed (S := (knownCycleMembers : Set ℤ))
        (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
  have hnorb : ∀ a ∈ ({0, 1, 2, 4, 44, 8} : Finset ℤ),
      amusicalOrbit n ≠ amusicalOrbit a := by
    intro a ha heq
    apply hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl (hclosed _ (by decide) (heq ▸ mem_amusicalOrbit_self n))
      | exact Or.inr (heq ▸ mem_amusicalOrbit_self n)
  refine ⟨insert n {0, 1, 2, 4, 44, 8}, ?_, ?_, ?_⟩
  · have : n ∉ ({0, 1, 2, 4, 44, 8} : Finset ℤ) := by
      intro hn'
      exact hnorb n (by simpa using hn') rfl
    simp [this]
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hn0
    · simp only [Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro a ha b hb hab
    change a ∈ (insert n {0, 1, 2, 4, 44, 8} : Finset ℤ) at ha
    change b ∈ (insert n {0, 1, 2, 4, 44, 8} : Finset ℤ) at hb
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hnorb b (Finset.mem_insert.mp hb |>.resolve_left hab.symm)
    · rcases Finset.mem_insert.mp hb with hbn | hb
      · subst b
        exact (hnorb a ha).symm
      · exact amusical_six_distinct_orbits a ha b hb hab

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
