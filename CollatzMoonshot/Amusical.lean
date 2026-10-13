/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Collatz's original permutation (Conway's "amusical permutation")

`U(2n) = 3n`, `U(4n+1) = 3n+1`, `U(4n+3) = 3n+2`, a permutation of `ℤ`.  The open question is
whether the orbit of `8` is infinite.

Sources:
* Lagarias, arXiv:2111.02635v1: one of Collatz's original problems from the 1930s; the
  question about `n = 8` was raised by Murray Klamkin in 1963 and "remains unsolved".
* Conway, *On unsettleable arithmetical problems*, Amer. Math. Monthly 120 (2013) 192-198
  (summary: `papers/2013-conway-unsettleable-summary.md`).  He writes the same map as
  `2k ↦ 3k, 4k+1 ↦ 3k+1, 4k−1 ↦ 3k−1` and offers "8 lies on an infinite cycle" as his candidate
  for the simplest unsettleable statement.

The defining equations are `amusical_two_mul`, `amusical_four_mul_add_one` and
`amusical_four_mul_add_three`; the permutation is `amusicalPerm`; the open problem is the node
`AmusicalOrbitOfEightInfinite`, with `amusicalOrbitOfEightInfinite_iff` reducing it to
"`8` is not a periodic point".
-/

namespace CollatzMoonshot.Amusical

/-- Collatz's permutation `U` on `ℤ`. -/
def amusical (n : ℤ) : ℤ :=
  if n % 2 = 0 then 3 * (n / 2)
  else if n % 4 = 1 then 3 * (n / 4) + 1
  else 3 * (n / 4) + 2

/-- The inverse of `amusical`: `3m ↦ 2m`, `3m+1 ↦ 4m+1`, `3m+2 ↦ 4m+3`. -/
def amusicalInv (m : ℤ) : ℤ :=
  if m % 3 = 0 then 2 * (m / 3)
  else if m % 3 = 1 then 4 * (m / 3) + 1
  else 4 * (m / 3) + 3

theorem amusical_two_mul (n : ℤ) : amusical (2 * n) = 3 * n := by
  unfold amusical; split_ifs <;> omega

theorem amusical_four_mul_add_one (n : ℤ) : amusical (4 * n + 1) = 3 * n + 1 := by
  unfold amusical; split_ifs <;> omega

theorem amusical_four_mul_add_three (n : ℤ) : amusical (4 * n + 3) = 3 * n + 2 := by
  unfold amusical; split_ifs <;> omega

theorem amusicalInv_amusical (n : ℤ) : amusicalInv (amusical n) = n := by
  unfold amusical amusicalInv; split_ifs <;> omega

theorem amusical_amusicalInv (m : ℤ) : amusical (amusicalInv m) = m := by
  unfold amusical amusicalInv; split_ifs <;> omega

/-- `U` is a permutation of `ℤ`. -/
def amusicalPerm : Equiv.Perm ℤ where
  toFun := amusical
  invFun := amusicalInv
  left_inv := amusicalInv_amusical
  right_inv := amusical_amusicalInv

theorem amusical_injective : Function.Injective amusical :=
  amusicalPerm.injective

/-- The first thirteen steps from `8`: `8, 12, 18, 27, 20, 30, 45, 34, 51, 38, 57, 43, 32, 48`. -/
theorem amusical_orbit_eight_prefix :
    (List.range 14).map (fun k => amusical^[k] 8) =
      [8, 12, 18, 27, 20, 30, 45, 34, 51, 38, 57, 43, 32, 48] := by
  decide

/-- **Open (Collatz 1930s, Klamkin 1963; Conway 2013 suggests it may be unsettleable).**
The forward orbit of `8` under `U` is infinite.

Believed true.  Heuristic: on a random integer `U` multiplies by `3/2` with probability `1/2` and
by `3/4` with probability `1/2`, a geometric-mean drift of `(9/8)^(1/2) ≈ 1.061` per step, so
orbits should escape to infinity.  Numerics (2026-10-12, Python): no return to `8` within
`2·10^5` steps, by which point the iterate has 5224 digits, against `2·10^5 · log₁₀ 1.061 ≈ 5100`
predicted by the drift.  Control: the same loop started at `2` finds the cycle `2 → 3 → 2`.
Unlike `3x+1`, the drift points *up*, so there is no descent mechanism to prove the statement,
and a proof would need to rule out every return at once. -/
def AmusicalOrbitOfEightInfinite : Prop :=
  (Set.range fun k : ℕ => amusical^[k] 8).Infinite

/-- Because `U` is injective, the orbit of `8` is infinite exactly when `8` never returns. -/
theorem amusicalOrbitOfEightInfinite_iff :
    AmusicalOrbitOfEightInfinite ↔ ∀ k : ℕ, 0 < k → amusical^[k] 8 ≠ 8 := by
  constructor
  · intro hinf k hk hper
    apply hinf
    apply ((Finset.range k).image fun i => amusical^[i] 8).finite_toSet.subset
    rintro _ ⟨m, rfl⟩
    have hp : Function.IsPeriodicPt amusical k 8 := hper
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨m % k, Nat.mod_lt _ hk, hp.iterate_mod_apply m⟩
  · intro hnot hfin
    have hninj : ¬ Function.Injective fun k : ℕ => amusical^[k] 8 :=
      fun hinj => Set.infinite_range_of_injective hinj hfin
    simp only [Function.Injective, not_forall] at hninj
    obtain ⟨i, j, hij, hne⟩ := hninj
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · apply hnot (j - i) (by omega)
      apply (amusical_injective.iterate i)
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' h.le]
      exact hij.symm
    · apply hnot (i - j) (by omega)
      apply (amusical_injective.iterate j)
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' h.le]
      exact hij

/-! ## Drift: the even-step share along the orbit of `8`

Even steps multiply by exactly `3/2`; odd steps by `3/4 ± 1/(4x)`.  For large values the orbit
grows iff the share of even steps exceeds `log₂(4/3) ≈ 0.415`.  That threshold is only a
large-value statement: `amusical_small_cycles` exhibits the cycle `2 → 3 → 2` with even share
`1/2` and the cycle `4 → 6 → 9 → 7 → 5 → 4` with share `2/5`.  The orbit of `8` avoids every
small cycle, so its values stay `≥ 4` and the odd-step ratios stay in `[11/16, 13/16]`; that
is the content of `periodic_eight_even_bound`. -/

/-- The cycles of `U` below `10`: the fixed points `0, 1`, the 2-cycle `{2, 3}` and the 5-cycle
`{4, 6, 9, 7, 5}`.  `8` lies on none of them. -/
theorem amusical_small_cycles :
    amusical 0 = 0 ∧ amusical 1 = 1 ∧ amusical 2 = 3 ∧ amusical 3 = 2 ∧
      amusical 4 = 6 ∧ amusical 6 = 9 ∧ amusical 9 = 7 ∧ amusical 7 = 5 ∧ amusical 5 = 4 := by
  decide

/-- The number of even values among `U^[0] 8, …, U^[k-1] 8`. -/
def evenCount (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun i => amusical^[i] 8 % 2 = 0).card

/-- **Believed (~95%), proof not yet written.**  If `8` were periodic with period `p` and `e`
even steps per period, then `(3/2)^e (11/16)^(p-e) ≤ 1`.

English proof: the orbit of `8` is positive and avoids the invariant set `{0, 1, 2, 3}` (a
bijection's cycles are disjoint, and `8` is not in them), so every value is `≥ 4`.  An odd step
from `x` multiplies by `3/4 ± 1/(4x) ≥ 11/16`.  Around a cycle the product of the step ratios
is `1`, so `1 ≥ (3/2)^e (11/16)^(p-e)`. -/
theorem periodic_eight_even_bound {p : ℕ} (hp : 0 < p) (hper : amusical^[p] 8 = 8) :
    3 ^ evenCount p * 11 ^ (p - evenCount p) ≤ 2 ^ evenCount p * 16 ^ (p - evenCount p) := by
  sorry

/-- **Open, normality-type.**  The even values have density `1/2` along the orbit of `8`.

This is the heuristic behind `AmusicalOrbitOfEightInfinite`: if the orbit's residues mod `4`
look like independent fair digits, the evens have density `1/2`, well above the large-value
threshold `log₂(4/3) ≈ 0.415`.  It is a frequency statement about one specific orbit, the same
kind of statement as the normality of a specific real number. -/
def EightEvenDensityHalf : Prop :=
  Filter.Tendsto (fun k : ℕ => (evenCount k : ℝ) / k) Filter.atTop (nhds (1 / 2))

/-- **Believed (~95%), proof not yet written.**  Even density `1/2` forces the orbit of `8` to be
infinite.

English proof: if `8` had period `p` with `e` even steps per period, then
`evenCount (m * p) = m * e`, so the density would be `e / p`, forcing `2e = p`.  Then
`periodic_eight_even_bound` gives `33^e ≤ 32^e`, so `e = 0` and `p = 0`, a contradiction. -/
theorem amusicalOrbitOfEightInfinite_of_evenDensityHalf (h : EightEvenDensityHalf) :
    AmusicalOrbitOfEightInfinite := by
  sorry

end CollatzMoonshot.Amusical
