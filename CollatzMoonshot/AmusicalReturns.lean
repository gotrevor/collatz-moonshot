/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical

/-!
# Returns, exits and residues: witnesses for the closed amusical routes

Statements from the 2026-10-13 research agents (reports in `RESEARCH-2026-10-13-amusical-
single-chain.md` §7), each proved on paper there.  Treadmill target
(`KICKOFF-2026-10-13-amusical-returns.md`): close every `sorry` in this file.

* `exists_large_nonOrbitMin`: every residue class mod `2^k 3^l` contains arbitrarily large
  non-minima, so no congruence certifies an orbit minimum (the provable half of
  `MinimaNotResidueDetermined`).
* `exits_eq_strictMinima`: the points of `[1, X]` that never come back are exactly as many as the
  strict orbit minima in `[1, X]` (true for any such bijection, so not a lever by itself).
* `exists_denseLinearReturns_of_finitelyManyOrbits`: the strongest form of the linear-recurrence
  reduction.
* `return_defect_bound`: at a return the linear form `n log 2 − j log 3 + log(y/x)` is only
  `O(log j)`, not small, which is why Baker-type bounds give nothing.
-/

namespace CollatzMoonshot.Amusical

/-- **Target.**  Every residue class mod `2^k 3^l` has arbitrarily large non-minima.  Paper
proof: by CRT choose `n` in the class whose 2-adic digits after the forced prefix make the next
`K` steps all of type `4m+1 ↦ 3m+1`, which contracts toward `1`; for `K` large compared with the
prefix length the orbit drops below `n`. -/
theorem exists_large_nonOrbitMin (k l c T : ℕ) :
    ∃ n : ℕ, T < n ∧ n ≡ c [MOD 2 ^ k * 3 ^ l] ∧ ¬ IsOrbitMin (n : ℤ) := by
  sorry

open Classical in
/-- **Target.**  Exits equal strict minima: each infinite orbit meeting `[1, X]` has exactly one
last forward visit there and exactly one strict minimum there; cycles have neither. -/
theorem exits_eq_strictMinima (X : ℕ) :
    ((Finset.Icc 1 X).filter fun n : ℕ =>
        ∀ j : ℕ, 0 < j → (X : ℤ) < (amusicalPerm ^ (j : ℤ)) n).card =
      ((Finset.Icc 1 X).filter fun n : ℕ =>
        ∀ j : ℤ, j ≠ 0 → (n : ℤ) < (amusicalPerm ^ j) n).card := by
  sorry

/-- **Target.**  The strong form of the linear-recurrence reduction: finitely many orbits give an
infinite orbit with, for infinitely many `X`, at least `εX/2 − 1` times `j` with `|j| ≥ εX/4`
and value in `[0, X)`.  Equivalent to positive upper density of that orbit. -/
theorem exists_denseLinearReturns_of_finitelyManyOrbits (h : ¬ AmusicalInfinitelyManyOrbits) :
    ∃ x : ℤ, 0 ≤ x ∧ (amusicalOrbit x).Infinite ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ᶠ X : ℕ in Filter.atTop, ∃ S : Finset ℤ, ε * X / 2 - 1 ≤ S.card ∧
        ∀ j ∈ S, ε * X / 4 ≤ |(j : ℝ)| ∧ 0 ≤ (amusicalPerm ^ j) x ∧
          (amusicalPerm ^ j) x < X := by
  sorry

/-- The 2-adic weight of the first `j` steps from `x`: `1` per even step, `2` per odd step, so
`U^j x ≈ 3^j x / 2^(stepWeight x j)`. -/
def stepWeight (x : ℤ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, if amusical^[i] x % 2 = 0 then 1 else 2

/-- **Target.**  The return defect: along an aperiodic orbit from `x ≥ 2`, odd steps multiply by
`(3/4)(1 ± 1/(3z))` with distinct `z ≥ 2`, so the linear form in `log 2`, `log 3` and
`log (U^j x / x)` is at most `Σ_{z=2}^{j+1} 1/(3z−1) ≤ (1/3) log((6j+7)/7)`. -/
theorem return_defect_bound {x : ℤ} (hx : 2 ≤ x) (hinf : (amusicalOrbit x).Infinite) (j : ℕ) :
    |(stepWeight x j : ℝ) * Real.log 2 - j * Real.log 3 +
        Real.log ((amusical^[j] x : ℝ) / x)| ≤ 1 / 3 * Real.log ((6 * j + 7) / 7) := by
  sorry

end CollatzMoonshot.Amusical
