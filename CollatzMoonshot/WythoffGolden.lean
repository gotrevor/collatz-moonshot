/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.AmusicalTrap
import CollatzMoonshot.MonotonePotential
import CollatzMoonshot.WythoffGeneral
import CollatzMoonshot.WythoffCone

/-!
# The golden Wythoff member `α = 3 + √5`: 3-cycles and a Sturmian trap

Research note `wythoff-solvable`, §4 (b4) and §9.  `α = 3 + √5 = alphaK 3 (−1)` is the cone
member `(b, c) = (3, −1)` of Theorem K (`WythoffCone`) and the `m = 2` multinacci member
(`r = 1` boundary of Theorem G): `x = β/2 = 1/φ` is the root of `x³ − 2x + 1 = (x − 1)(x² + x − 1)`,
`β = √5 − 1 = 2/φ`.  Let `W = W_α` (`WythoffGeneral.wy`); then `W(2k) = 2k + ⌊2kφ⌋`
(`wy_gold_two_mul`), so `W(2k)` is even iff `{kφ} < 1/2` (`wy_gold_two_mul_even_iff`).

1. **3-cycles.**  If `n` is even and `W(n)` is odd, then `W²(n)` is odd and `W³(n) = n`
   (`wy_gold_odd_of_odd`, `wy_gold_iterate_three`), for every `n ∈ ℤ`: every point of the `E O`
   cylinder lies on a 3-cycle `{n, W n, W² n}`, with minimum `n` (`isOrbitMin_of_cycle_gold`).
2. **Sturmian trap.**  The cone set `S′ = coneSet 3 (−1) = {2k : k > 0, {kφ} < 1/2}`
   (`mem_coneSet_gold_iff`) is `W`-invariant (Theorem K, `coneSet_trap`); on it `W(2k) = 2k′`
   with `k′ = k + ⌊kφ⌋` and `{k′φ} = {kφ}/φ²` (`fract_gold_image`), so
   `W(S′) = {2k′ : k′ > 0, {k′φ} < 1/(2φ²)}` (`mem_image_coneSet_gold_iff`): an irrational
   (Bohr-set) trap.
3. **Classification** (Lemma P with `S` = evens, `Φ = {z | W³ z = z}`, `T = 1`;
   `hyp_goldPerm`).  Every orbit through `ℕ⁺` is `{1}`, a 3-cycle, or infinite, tending to `∞`
   both ways and meeting `S′` (`goldPerm_trichotomy`).  The orbit minima in `ℕ⁺` are exactly
   `{1} ∪ {2k : {kφ} ≥ 1/(2φ²)}` (`isOrbitMin_goldPerm_iff`): the 3-cycle minima are the
   `2k` with `{kφ} ≥ 1/2`, and the infinite-orbit minima the `2k` with
   `1/(2φ²) ≤ {kφ} < 1/2` (`isOrbitMin_and_infinite_iff`), which are exactly Theorem K's entry
   points `S′ ∖ W(S′)` (`mem_coneEntry_gold_iff`).
4. **Counts.**  `#{minima ≤ X} = 1 + #{k ≤ X/2 : {kφ} ≥ 1/(2φ²)}` exactly
   (`minCount_goldPerm_eq`); infinitely many 3-cycles (unconditional,
   `goldCycleEvens_infinite`) and infinitely many infinite orbits (Theorem K); conditional on
   one-dimensional Weyl equidistribution (a literature hypothesis), the 3-cycle minima have
   density `1/4` and the infinite-orbit minima density `1/(4φ)`.

**Paper proofs of 1-2** (research note §4 (b4)).  Write `u = {kφ}`, `2kφ = k + k√5`.
* `W(2k) = ⌊k(3 + √5)⌋ = 2k + ⌊k + k√5⌋ = 2k + ⌊2kφ⌋ = 2k + 2⌊kφ⌋ + [u ≥ 1/2]`.
* *EO ⇒ EOO.*  If `u ≥ 1/2`, `v = W(2k) = 2j − 1` with `j = k + ⌊kφ⌋ + 1` (`j ≠ 0`: `j = 0`
  would need `k(1 + φ) ∈ [−1, 0)`), and `W(v) = ⌈jβ⌉ − 1 = ⌊2j(φ − 1)⌋ = ⌊2jφ⌋ − 2j`
  (`jβ ∉ ℤ`), whose parity is `[{jφ} ≥ 1/2]`.  Using `φ² = φ + 1`:
  `jφ = kφ + (kφ − u)φ + φ = 2kφ + k − uφ + φ ≡ u(2 − φ) + φ (mod 1)`, and for `u ∈ [1/2, 1)`,
  `u(2 − φ) + φ ∈ [1.809, 2)`, so `{jφ} ≥ 0.809`: `W²(2k)` is odd.
* *`W³ = n` on `E O O`.*  The sandwich of `WythoffLine` with `A = α/2`, `x = 1/φ`:
  `c_2 = A x² = x³/(2x − 1) = 1` and `x + x² = 1`, so `n < y_3 < n + 1` (the floor step is strict
  on the left, the odd steps on the right) and `W³(n) = ⌈y_3⌉ − 1 = n`.
* *Trap phase.*  If `u < 1/2`, `W(2k) = 2(k + ⌊kφ⌋)` and
  `(k + ⌊kφ⌋)φ = kφ + (kφ − u)φ ≡ 2u − uφ = u(2 − φ) = u/φ² (mod 1)`, with `u/φ² ∈ [0, 1)`.
  Conversely `k′ = ⌊kφ²⌋` for some `k` iff `{k′/φ²} > 1 − 1/φ²` iff `{k′φ} < 1/φ²`
  (`k′/φ² = 2k′ − k′φ`), and then `u = φ²{k′φ}`; so `k′ ∈ W(S′)/2` iff `{k′φ} < 1/(2φ²)`.

Truth checks: `tmp/drafter-Y/check.py` (exact `isqrt` arithmetic in `ℚ(√5)`, cross-checked
pointwise against certified interval arithmetic; brute-force minima for `y ≤ 2·10⁴`; census
154 509 infinite-orbit minima `≤ 10⁶` against `X/(4φ) = 154 508.5`, as in the research note).
-/

namespace CollatzMoonshot.WythoffGolden

open CollatzMoonshot.WythoffGeneral CollatzMoonshot.MonotonePotential
open CollatzMoonshot.WythoffCone
open CollatzMoonshot.AmusicalTrap (permOrbit InfinitelyManyInfiniteOrbits)
open Filter Topology Real
open scoped goldenRatio

/-- `W = W_α` for `α = 3 + √5 = alphaK 3 (−1)`. -/
local notation "Wg" => wy (alphaK 3 (-1))

/-! ## The parameter -/

/-- **(proved).**  `alphaK 3 (−1) = 3 + √5` (`9 − 4 = 5`). -/
theorem alphaK_three_neg_one : alphaK 3 (-1) = 3 + √5 := by
  unfold alphaK; norm_num

/-- **(proved).**  `3 + √5 = 2 + 2φ` (`φ = (1 + √5)/2`). -/
theorem alphaK_three_neg_one_eq_gold : alphaK 3 (-1) = 2 + 2 * φ := by
  unfold alphaK goldenRatio; norm_num; ring

/-- `W_{3+√5}` as a permutation of `ℤ`: the cone member `(b, c) = (3, −1)`. -/
noncomputable def goldPerm : Equiv.Perm ℤ :=
  wkPerm 3 (-1) (by norm_num) (by norm_num)

theorem goldPerm_apply (n : ℤ) : goldPerm n = Wg n := rfl

/-! ## The even branch and the 3-cycles -/

/-- **(drafted, 99%).**  `W(2k) = 2k + ⌊2kφ⌋` (`wy_two_mul`, `alphaK_three_neg_one_eq_gold`,
`Int.floor_intCast_add`). -/
theorem wy_gold_two_mul (k : ℤ) : Wg (2 * k) = 2 * k + ⌊2 * (k : ℝ) * φ⌋ := by
  sorry

/-- **(drafted, 99%).**  `W(2k)` is even iff `{kφ} < 1/2`
(`⌊2kφ⌋ = 2⌊kφ⌋ + ⌊2{kφ}⌋`). -/
theorem wy_gold_two_mul_even_iff (k : ℤ) :
    Wg (2 * k) % 2 = 0 ↔ Int.fract ((k : ℝ) * φ) < 1 / 2 := by
  sorry

/-- **(drafted, 97%; EO ⇒ EOO).**  If `n` is even and `W(n)` is odd, `W²(n)` is odd; for every
`n ∈ ℤ`.  Paper proof: module docstring (the next phase is `{u(2 − φ) + φ} ≥ 0.809`). -/
theorem wy_gold_odd_of_odd {n : ℤ} (hn : n % 2 = 0) (h : Wg n % 2 = 1) : Wg (Wg n) % 2 = 1 := by
  sorry

/-- **(drafted, 98%; 3-cycles).**  If `n` is even and `W(n)` is odd, then `W³(n) = n`; for every
`n ∈ ℤ`.  Paper proof: the `WythoffLine` sandwich with `c_2 = 1`, `x + x² = 1`, after
`wy_gold_odd_of_odd` (module docstring). -/
theorem wy_gold_iterate_three {n : ℤ} (hn : n % 2 = 0) (h : Wg n % 2 = 1) : Wg^[3] n = n := by
  sorry

/-- **(drafted, 98%).**  For `n > 0` even with `W(n)` odd, `n` is the minimum of its (3-cycle)
orbit.  Paper proof: the orbit is `{n, W n, W² n}` (`wy_gold_iterate_three`); `W n > n`
(`lt_wy_of_even`), and `W² n` is odd, positive and `≠ 1` (else `n = W³ n = 1`), so
`n = W(W² n) < W² n` (`wy_lt_of_odd`). -/
theorem isOrbitMin_of_cycle_gold {n : ℤ} (hn0 : 0 < n) (hn : n % 2 = 0) (h : Wg n % 2 = 1) :
    IsOrbitMin goldPerm n := by
  sorry

/-- **(drafted, 98%; infinitely many 3-cycles, unconditional).**  Infinitely many `n > 0` are
even with `W(n)` odd, each the minimum of its own 3-cycle.  Paper proof: among any three
consecutive `k ≥ 1` one has `{kφ} ≥ 1/2`: `{(k + 1)φ} = {kφ + (φ − 1)}`, `φ − 1 ≈ 0.618`; if
`u = {kφ} < 0.382` the next phase is `u + 0.618 ∈ [0.618, 1)`, and if `u ∈ [0.382, 1/2)` the
next is `u − 0.382 < 0.118` and the one after lies in `[0.618, 0.736)`
(`wy_gold_two_mul_even_iff`). -/
theorem goldCycleEvens_infinite : {n : ℤ | 0 < n ∧ n % 2 = 0 ∧ Wg n % 2 = 1}.Infinite := by
  sorry

/-! ## The Sturmian trap `S′ = coneSet 3 (−1)` -/

/-- **(drafted, 99%).**  `S′ = {2k : k > 0, {kφ} < 1/2}` (`wy_gold_two_mul_even_iff`). -/
theorem mem_coneSet_gold_iff (n : ℤ) :
    n ∈ coneSet 3 (-1) ↔ ∃ k : ℤ, 0 < k ∧ n = 2 * k ∧ Int.fract ((k : ℝ) * φ) < 1 / 2 := by
  sorry

/-- **(proved: an instance of Theorem K).**  `S′` is `W`-invariant. -/
theorem goldPerm_mapsTo_coneSet : ∀ n ∈ coneSet 3 (-1), goldPerm n ∈ coneSet 3 (-1) :=
  coneSet_trap _ _

/-- **(drafted, 98%; the Sturmian rotation).**  If `{kφ} < 1/2` then `W(2k) = 2k′` with
`k′ = k + ⌊kφ⌋` and `{k′φ} = {kφ}/φ²`; for every `k ∈ ℤ`.  Paper proof: module docstring
(`φ² = φ + 1`, `1/φ² = 2 − φ`, `Int.fract_eq_iff`). -/
theorem fract_gold_image {k : ℤ} (hk : Int.fract ((k : ℝ) * φ) < 1 / 2) :
    Wg (2 * k) = 2 * (k + ⌊(k : ℝ) * φ⌋) ∧
      Int.fract (((k + ⌊(k : ℝ) * φ⌋ : ℤ) : ℝ) * φ) = Int.fract ((k : ℝ) * φ) / φ ^ 2 := by
  sorry

/-- **(drafted, 96%).**  `W(S′) = {2k′ : k′ > 0, {k′φ} < 1/(2φ²)}`.  Paper proof: `⊆` by
`fract_gold_image`; `⊇`: for `{k′φ} < 1/(2φ²)` put `k = ⌈k′/φ²⌉`; then `k′ = ⌊kφ²⌋ = k + ⌊kφ⌋`
(module docstring; `k′/φ² = 2k′ − k′φ`, so `{k′/φ²} = 1 − {k′φ} > 1 − 1/φ²`), `k ≥ 1`, and
`{kφ} = φ²{k′φ} < 1/2` (`fract_gold_image` read backward). -/
theorem mem_image_coneSet_gold_iff (n : ℤ) :
    n ∈ goldPerm '' coneSet 3 (-1) ↔
      ∃ k : ℤ, 0 < k ∧ n = 2 * k ∧ Int.fract ((k : ℝ) * φ) < 1 / (2 * φ ^ 2) := by
  sorry

/-! ## Classification via Lemma P -/

/-- The exceptional set `Φ = {z | W³ z = z}`: in `ℕ⁺`, the fixed point `1` and the 3-cycles
(`mem_goldCycles_iff`). -/
def goldCycles : Set ℤ :=
  {z | Wg^[3] z = z}

/-- **(drafted, 97%).**  The positive points of `Φ` are `1` and the points of the 3-cycles
`{n, W n, W² n}`, `n > 0` even with `W n` odd.  Paper proof: `⊇` by `wy_one` and
`wy_gold_iterate_three` (`W³` commutes with `W`).  `⊆`: a positive cycle of length dividing `3`
other than `{1}` contains an even point (odd points `≥ 3` step down, `wy_lt_of_odd`); if
`W` of that even point were even, the orbit would enter the trap `S′`, where `W` strictly
increases (`lt_wy_of_even`), so it could not return. -/
theorem mem_goldCycles_iff {z : ℤ} (hz : 0 < z) :
    z ∈ goldCycles ↔ z = 1 ∨ ∃ n : ℤ, 0 < n ∧ n % 2 = 0 ∧ Wg n % 2 = 1 ∧
      (z = n ∨ z = Wg n ∨ z = Wg^[2] n) := by
  sorry

/-- **(drafted, 97%).**  Lemma P applies with `S` = evens, `Φ = {z | W³ z = z}`, `T = 1`.  Paper
proof: `pos_iff` is `wy_pos_iff`; `mem_fix_iff`: `W³(W z) = W(W³ z)` and injectivity; (H1): a
positive odd `z ∉ Φ` has `z ≠ 1` (`wy_one`), so `W z < z` (`wy_lt_of_odd`); (H2) with `τ = 1`: a
positive even `s ∉ Φ` has `W s` even (else `W³ s = s`, `wy_gold_iterate_three`) and `W s > s`
(`lt_wy_of_even`). -/
theorem hyp_goldPerm : Hyp goldPerm {n | n % 2 = 0} goldCycles 1 := by
  sorry

/-- **(drafted, 97%).**  For `x > 0`: the orbit is finite iff `x ∈ Φ`.  Paper proof: `x ∈ Φ`
gives an orbit inside `{x, W x, W² x}`; `x ∉ Φ` gives `permOrbit_infinite` (`hyp_goldPerm`). -/
theorem permOrbit_goldPerm_finite_iff {x : ℤ} (hx : 0 < x) :
    (permOrbit goldPerm x).Finite ↔ x ∈ goldCycles := by
  sorry

/-- **(drafted, 97%; forward escape off the cycles).** -/
theorem tendsto_goldPerm_pow {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ goldCycles) :
    Tendsto (fun n : ℕ => (goldPerm ^ n) x) atTop atTop := by
  sorry

/-- **(drafted, 97%; backward escape off the cycles).** -/
theorem tendsto_goldPerm_pow_neg {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ goldCycles) :
    Tendsto (fun n : ℕ => (goldPerm ^ (-(n : ℤ))) x) atTop atTop := by
  sorry

/-- **(drafted, 97%).**  An orbit through a positive point off `Φ` meets the trap `S′`.  Paper
proof: its minimum `y` (`exists_isOrbitMin`) is even (`isOrbitMin_iff`) and off `Φ`, so `W y` is
even (`hyp_goldPerm`'s (H2) argument): `y ∈ S′`. -/
theorem exists_mem_orbit_mem_coneSet_gold {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ goldCycles) :
    ∃ y ∈ permOrbit goldPerm x, y ∈ coneSet 3 (-1) := by
  sorry

/-- **(drafted, 96%; classification).**  Every orbit through `ℕ⁺` is `{1}`, a 3-cycle
`{n, W n, W² n}` (`n > 0` even, `W n` odd), or infinite, tending to `∞` in both time directions
and meeting the trap `S′`.  Paper proof: `mem_goldCycles_iff` and
`permOrbit_eq_singleton_of_fixed` for `x ∈ Φ`; `permOrbit_goldPerm_finite_iff`,
`tendsto_goldPerm_pow(_neg)`, `exists_mem_orbit_mem_coneSet_gold` otherwise. -/
theorem goldPerm_trichotomy {x : ℤ} (hx : 0 < x) :
    permOrbit goldPerm x = {1} ∨
      (∃ n : ℤ, 0 < n ∧ n % 2 = 0 ∧ Wg n % 2 = 1 ∧ permOrbit goldPerm x = {n, Wg n, Wg^[2] n}) ∨
      ((permOrbit goldPerm x).Infinite ∧
        Tendsto (fun n : ℕ => (goldPerm ^ n) x) atTop atTop ∧
        Tendsto (fun n : ℕ => (goldPerm ^ (-(n : ℤ))) x) atTop atTop ∧
        ∃ y ∈ permOrbit goldPerm x, y ∈ coneSet 3 (-1)) := by
  sorry

/-- **(drafted, 97%; Lemma P minimum test, `T = 1`).**  For `x > 0` off `Φ`: `x` is the minimum
of its orbit iff `x` is even and `W⁻¹(x)` is odd (`isOrbitMin_iff`, `zpow_neg_one`). -/
theorem isOrbitMin_goldPerm_iff_pred {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ goldCycles) :
    IsOrbitMin goldPerm x ↔ x % 2 = 0 ∧ goldPerm.symm x % 2 = 1 := by
  sorry

/-- **(drafted, 96%; infinite-orbit minima, explicit).**  For `x > 0`: `x` is the minimum of an
infinite orbit iff `x = 2k` with `1/(2φ²) ≤ {kφ} < 1/2`.  Paper proof: off `Φ`, the minima are the
`x ∈ S′` with `W⁻¹ x` odd (`isOrbitMin_goldPerm_iff_pred`, `hyp_goldPerm`), i.e. `S′ ∖ W(S′)`
(`W⁻¹ x > 0` is even iff `W⁻¹ x ∈ S′`, as `W(W⁻¹ x) = x` is even); then
`mem_coneSet_gold_iff` and `mem_image_coneSet_gold_iff`.  Every such `x` has `W x` even, so it
is off `Φ`. -/
theorem isOrbitMin_and_infinite_iff {x : ℤ} (hx : 0 < x) :
    IsOrbitMin goldPerm x ∧ (permOrbit goldPerm x).Infinite ↔
      ∃ k : ℤ, x = 2 * k ∧ 1 / (2 * φ ^ 2) ≤ Int.fract ((k : ℝ) * φ) ∧
        Int.fract ((k : ℝ) * φ) < 1 / 2 := by
  sorry

/-- **(drafted, 97%; finite-orbit minima).**  For `x > 0`: `x` is the minimum of a finite orbit
iff `x = 1` or `x = 2k` with `{kφ} ≥ 1/2` (`mem_goldCycles_iff`, `isOrbitMin_of_cycle_gold`,
`wy_gold_two_mul_even_iff`; the odd points of a 3-cycle exceed its even point). -/
theorem isOrbitMin_and_finite_iff {x : ℤ} (hx : 0 < x) :
    IsOrbitMin goldPerm x ∧ (permOrbit goldPerm x).Finite ↔
      x = 1 ∨ ∃ k : ℤ, x = 2 * k ∧ 1 / 2 ≤ Int.fract ((k : ℝ) * φ) := by
  sorry

/-- **(drafted, 96%; all minima).**  For `x > 0`: `x` is an orbit minimum iff `x = 1` or `x = 2k`
with `{kφ} ≥ 1/(2φ²)` (`isOrbitMin_and_infinite_iff`, `isOrbitMin_and_finite_iff`). -/
theorem isOrbitMin_goldPerm_iff {x : ℤ} (hx : 0 < x) :
    IsOrbitMin goldPerm x ↔
      x = 1 ∨ ∃ k : ℤ, x = 2 * k ∧ 1 / (2 * φ ^ 2) ≤ Int.fract ((k : ℝ) * φ) := by
  sorry

/-- **(drafted, 96%; the infinite-orbit minima are Theorem K's entry points).**  `S′ ∖ W(S′)` is
exactly the set of positive minima of infinite orbits, so every infinite orbit enters the trap
at its minimum, and K's entry density `(1/4)(1 − 2/α) = 1/(4φ)` is attained.  Paper proof:
`mem_coneSet_gold_iff`, `mem_image_coneSet_gold_iff`, `isOrbitMin_and_infinite_iff`. -/
theorem mem_coneEntry_gold_iff (x : ℤ) :
    x ∈ coneSet 3 (-1) \ goldPerm '' coneSet 3 (-1) ↔
      0 < x ∧ IsOrbitMin goldPerm x ∧ (permOrbit goldPerm x).Infinite := by
  sorry

/-- **(proved: an instance of Theorem K).**  Infinitely many infinite orbits. -/
theorem goldPerm_infinitelyManyInfiniteOrbits : InfinitelyManyInfiniteOrbits goldPerm :=
  wkPerm_infinitelyManyInfiniteOrbits _ _

/-! ## Counts and densities -/

open Classical in
/-- The number of 3-cycle (and fixed-point) minima in `[1, X]`. -/
noncomputable def goldCycleMinCount (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun x =>
    IsOrbitMin goldPerm x ∧ (permOrbit goldPerm x).Finite).card

open Classical in
/-- The number of infinite-orbit minima in `[1, X]`. -/
noncomputable def goldInfMinCount (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun x =>
    IsOrbitMin goldPerm x ∧ (permOrbit goldPerm x).Infinite).card

open Classical in
/-- **(drafted, 96%; exact count).**  `#{minima ≤ X} = 1 + #{1 ≤ k ≤ X/2 : {kφ} ≥ 1/(2φ²)}`.
Paper proof: `isOrbitMin_goldPerm_iff`; the map `k ↦ 2k` is a bijection onto the even minima. -/
theorem minCount_goldPerm_eq {X : ℕ} (hX : 1 ≤ X) :
    minCount goldPerm X = 1 + ((Finset.Icc (1 : ℤ) ((X / 2 : ℕ) : ℤ)).filter
      fun k : ℤ => 1 / (2 * φ ^ 2) ≤ Int.fract ((k : ℝ) * φ)).card := by
  sorry

/-- **(drafted, 95%; 3-cycle density, conditional).**  Assuming one-dimensional Weyl
equidistribution (a literature hypothesis), the 3-cycle minima have density `1/4`.  Paper proof:
`isOrbitMin_and_finite_iff`: the count is `1 + #{k ≤ X/2 : {kφ} ∈ [1/2, 1)}`;
`WeylEquidistribution` with `θ = φ` (`goldenRatio_irrational`), `[a, b) = [1/2, 1)`, at
`N = ⌊X/2⌋`. -/
theorem tendsto_goldCycleMinCount (hW : WeylEquidistribution) :
    Tendsto (fun X : ℕ => (goldCycleMinCount X : ℝ) / X) atTop (𝓝 (1 / 4)) := by
  sorry

/-- **(drafted, 95%; infinite-orbit minima density, conditional).**  Assuming one-dimensional
Weyl equidistribution, the infinite-orbit minima have density `1/(4φ)`.  Paper proof:
`isOrbitMin_and_infinite_iff`, `WeylEquidistribution` with `[a, b) = [1/(2φ²), 1/2)`, of length
`(φ² − 1)/(2φ²) = 1/(2φ)`, at `N = ⌊X/2⌋`. -/
theorem tendsto_goldInfMinCount (hW : WeylEquidistribution) :
    Tendsto (fun X : ℕ => (goldInfMinCount X : ℝ) / X) atTop (𝓝 (1 / (4 * φ))) := by
  sorry

/-- **(drafted, 95%; total minima density, conditional).**  `1/4 + 1/(4φ) = 1/2 − 1/(4φ²)`
(`minCount = goldCycleMinCount + goldInfMinCount`, or directly from `minCount_goldPerm_eq`). -/
theorem tendsto_minCount_goldPerm (hW : WeylEquidistribution) :
    Tendsto (fun X : ℕ => (minCount goldPerm X : ℝ) / X) atTop (𝓝 (1 / 4 + 1 / (4 * φ))) := by
  sorry

end CollatzMoonshot.WythoffGolden
