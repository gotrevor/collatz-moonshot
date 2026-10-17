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

theorem gold_bounds : (1618 : ℝ) / 1000 < φ ∧ φ < 16181 / 10000 := by
  have h := goldenRatio_sq
  have hp := goldenRatio_pos
  constructor <;> nlinarith

/-- `β = α/(α − 1) = 2φ − 2` for `α = 2 + 2φ`. -/
theorem gold_beta : alphaK 3 (-1) / (alphaK 3 (-1) - 1) = 2 * φ - 2 := by
  rw [alphaK_three_neg_one_eq_gold]
  have hp := goldenRatio_pos
  have h : (2 + 2 * φ - 1) ≠ 0 := by linarith
  rw [div_eq_iff h]
  linear_combination (-4 : ℝ) * goldenRatio_sq

/-- `W(2m − 1) = ⌈m(2φ − 2)⌉ − 1`. -/
theorem wy_gold_two_mul_sub_one (m : ℤ) : Wg (2 * m - 1) = ⌈(m : ℝ) * (2 * φ - 2)⌉ - 1 := by
  rw [wy_two_mul_sub_one, gold_beta]

theorem floor_two_mul_of_lt {y : ℝ} (h : Int.fract y < 1 / 2) : ⌊2 * y⌋ = 2 * ⌊y⌋ := by
  rw [Int.floor_eq_iff]
  have := Int.fract_nonneg y
  unfold Int.fract at *
  push_cast
  constructor <;> linarith

theorem floor_two_mul_of_ge {y : ℝ} (h : 1 / 2 ≤ Int.fract y) : ⌊2 * y⌋ = 2 * ⌊y⌋ + 1 := by
  rw [Int.floor_eq_iff]
  have := Int.fract_lt_one y
  unfold Int.fract at *
  push_cast
  constructor <;> linarith

/-- **(drafted, 99%).**  `W(2k) = 2k + ⌊2kφ⌋` (`wy_two_mul`, `alphaK_three_neg_one_eq_gold`,
`Int.floor_intCast_add`). -/
theorem wy_gold_two_mul (k : ℤ) : Wg (2 * k) = 2 * k + ⌊2 * (k : ℝ) * φ⌋ := by
  rw [wy_two_mul, alphaK_three_neg_one_eq_gold,
    show (k : ℝ) * (2 + 2 * φ) = ((2 * k : ℤ) : ℝ) + 2 * (k : ℝ) * φ by push_cast; ring]
  exact Int.floor_intCast_add _ _

/-- **(drafted, 99%).**  `W(2k)` is even iff `{kφ} < 1/2`
(`⌊2kφ⌋ = 2⌊kφ⌋ + ⌊2{kφ}⌋`). -/
theorem wy_gold_two_mul_even_iff (k : ℤ) :
    Wg (2 * k) % 2 = 0 ↔ Int.fract ((k : ℝ) * φ) < 1 / 2 := by
  rw [wy_gold_two_mul, show 2 * (k : ℝ) * φ = 2 * ((k : ℝ) * φ) by ring]
  rcases lt_or_ge (Int.fract ((k : ℝ) * φ)) (1 / 2) with h | h
  · rw [floor_two_mul_of_lt h]; simp only [h, iff_true]; omega
  · rw [floor_two_mul_of_ge h]; simp only [not_lt.2 h, iff_false]; omega

/-- The 3-cycle through `2k` when `{kφ} ≥ 1/2`, explicitly (`F = ⌊kφ⌋`):
`2k ↦ 2(k + F) + 1 ↦ 2F + 1 ↦ 2k`. -/
theorem gold_cycle (k : ℤ) (hu : 1 / 2 ≤ Int.fract ((k : ℝ) * φ)) :
    Wg (2 * k) = 2 * (k + ⌊(k : ℝ) * φ⌋) + 1 ∧
      Wg (2 * (k + ⌊(k : ℝ) * φ⌋) + 1) = 2 * ⌊(k : ℝ) * φ⌋ + 1 ∧
      Wg (2 * ⌊(k : ℝ) * φ⌋ + 1) = 2 * k := by
  have hg := gold_bounds
  have hsq := goldenRatio_sq
  have hkF : (k : ℝ) * φ = ⌊(k : ℝ) * φ⌋ + Int.fract ((k : ℝ) * φ) :=
    (Int.floor_add_fract _).symm
  have hu1 := Int.fract_lt_one ((k : ℝ) * φ)
  set F := ⌊(k : ℝ) * φ⌋ with hF
  set u := Int.fract ((k : ℝ) * φ) with hu_def
  refine ⟨?_, ?_, ?_⟩
  · rw [wy_gold_two_mul, show 2 * (k : ℝ) * φ = 2 * ((k : ℝ) * φ) by ring,
      floor_two_mul_of_ge hu]
    ring
  · rw [show 2 * (k + F) + 1 = 2 * (k + F + 1) - 1 by ring, wy_gold_two_mul_sub_one]
    have hid : ((k + F + 1 : ℤ) : ℝ) * (2 * φ - 2) = 2 * F + 2 * (u * (2 - φ) + φ - 1) := by
      push_cast
      linear_combination (4 - 2 * φ) * hkF + 2 * (k : ℝ) * hsq
    have hw1 : 0 ≤ u * (2 - φ) := mul_nonneg (Int.fract_nonneg _) (by linarith)
    have hw2 : u * (2 - φ) < 2 - φ := by nlinarith
    have : ⌈((k + F + 1 : ℤ) : ℝ) * (2 * φ - 2)⌉ = 2 * F + 2 := by
      rw [Int.ceil_eq_iff, hid]; push_cast; constructor <;> linarith
    rw [this]; ring
  · rw [show 2 * F + 1 = 2 * (F + 1) - 1 by ring, wy_gold_two_mul_sub_one]
    have hid : ((F + 1 : ℤ) : ℝ) * (2 * φ - 2) = 2 * k + 2 * ((φ - 1) * (1 - u)) := by
      push_cast
      linear_combination (2 - 2 * φ) * hkF + 2 * (k : ℝ) * hsq
    have hw1 : 0 < (φ - 1) * (1 - u) := mul_pos (by linarith) (by linarith)
    have hw2 : (φ - 1) * (1 - u) ≤ 1 / 2 := by nlinarith
    have : ⌈((F + 1 : ℤ) : ℝ) * (2 * φ - 2)⌉ = 2 * k + 1 := by
      rw [Int.ceil_eq_iff, hid]; push_cast; constructor <;> linarith
    rw [this]; ring

theorem fract_ge_of_odd {n : ℤ} (hn : n % 2 = 0) (h : Wg n % 2 = 1) :
    1 / 2 ≤ Int.fract (((n / 2 : ℤ) : ℝ) * φ) := by
  have hn2 : n = 2 * (n / 2) := by omega
  rw [hn2] at h
  by_contra hc
  have := (wy_gold_two_mul_even_iff (n / 2)).2 (not_le.1 hc)
  omega

/-- **(drafted, 97%; EO ⇒ EOO).**  If `n` is even and `W(n)` is odd, `W²(n)` is odd; for every
`n ∈ ℤ`.  Paper proof: module docstring (the next phase is `{u(2 − φ) + φ} ≥ 0.809`). -/
theorem wy_gold_odd_of_odd {n : ℤ} (hn : n % 2 = 0) (h : Wg n % 2 = 1) : Wg (Wg n) % 2 = 1 := by
  obtain ⟨h1, h2, -⟩ := gold_cycle _ (fract_ge_of_odd hn h)
  have hn2 : n = 2 * (n / 2) := by omega
  rw [hn2, h1, h2]
  omega

/-- **(drafted, 98%; 3-cycles).**  If `n` is even and `W(n)` is odd, then `W³(n) = n`; for every
`n ∈ ℤ`.  Paper proof: the `WythoffLine` sandwich with `c_2 = 1`, `x + x² = 1`, after
`wy_gold_odd_of_odd` (module docstring). -/
theorem wy_gold_iterate_three {n : ℤ} (hn : n % 2 = 0) (h : Wg n % 2 = 1) : Wg^[3] n = n := by
  obtain ⟨h1, h2, h3⟩ := gold_cycle _ (fract_ge_of_odd hn h)
  have hn2 : n = 2 * (n / 2) := by omega
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  conv_lhs => rw [hn2]
  rw [h1, h2, h3, ← hn2]

/-- Orbits stay in a set closed under `σ` and `σ⁻¹`. -/
theorem zpow_mem_of_closed (σ : Equiv.Perm ℤ) {C : Set ℤ} (h1 : ∀ x ∈ C, σ x ∈ C)
    (h2 : ∀ x ∈ C, σ.symm x ∈ C) (m : ℤ) : ∀ x ∈ C, (σ ^ m) x ∈ C := by
  induction m using Int.induction_on with
  | zero => intro x hx; simpa using hx
  | succ m ih =>
    intro x hx
    rw [zpow_add_one, Equiv.Perm.mul_apply]
    exact ih _ (h1 x hx)
  | pred m ih =>
    intro x hx
    rw [zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    exact ih _ (h2 x hx)

/-- **(drafted, 98%).**  For `n > 0` even with `W(n)` odd, `n` is the minimum of its (3-cycle)
orbit.  Paper proof: the orbit is `{n, W n, W² n}` (`wy_gold_iterate_three`); `W n > n`
(`lt_wy_of_even`), and `W² n` is odd, positive and `≠ 1` (else `n = W³ n = 1`), so
`n = W(W² n) < W² n` (`wy_lt_of_odd`). -/
theorem isOrbitMin_of_cycle_gold {n : ℤ} (hn0 : 0 < n) (hn : n % 2 = 0) (h : Wg n % 2 = 1) :
    IsOrbitMin goldPerm n := by
  have hg := gold_bounds
  obtain ⟨h1, h2, h3⟩ := gold_cycle _ (fract_ge_of_odd hn h)
  have hn2 : n = 2 * (n / 2) := by omega
  set k := n / 2 with hk
  set F := ⌊(k : ℝ) * φ⌋ with hF
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hFk : k ≤ F := by
    rw [hF, Int.le_floor]; nlinarith
  set C : Set ℤ := {n, 2 * (k + F) + 1, 2 * F + 1} with hC
  have hσ : ∀ x ∈ C, goldPerm x ∈ C := by
    intro x hx
    simp only [hC, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · rw [goldPerm_apply, hn2, h1]; simp
    · rw [goldPerm_apply, h2]; simp
    · rw [goldPerm_apply, h3, ← hn2]; simp
  have hσ' : ∀ x ∈ C, goldPerm.symm x ∈ C := by
    intro x hx
    simp only [hC, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · right; right
      rw [Equiv.symm_apply_eq, goldPerm_apply, h3, ← hn2]
    · left
      rw [Equiv.symm_apply_eq, goldPerm_apply, hn2, h1]
    · right; left
      rw [Equiv.symm_apply_eq, goldPerm_apply, h2]
  rintro y ⟨m, rfl⟩
  show n ≤ (goldPerm ^ m) n
  have := zpow_mem_of_closed goldPerm hσ hσ' m n (by simp [hC])
  simp only [hC, Set.mem_insert_iff, Set.mem_singleton_iff] at this
  omega

/-- **(drafted, 98%; infinitely many 3-cycles, unconditional).**  Infinitely many `n > 0` are
even with `W(n)` odd, each the minimum of its own 3-cycle.  Paper proof: among any three
consecutive `k ≥ 1` one has `{kφ} ≥ 1/2`: `{(k + 1)φ} = {kφ + (φ − 1)}`, `φ − 1 ≈ 0.618`; if
`u = {kφ} < 0.382` the next phase is `u + 0.618 ∈ [0.618, 1)`, and if `u ∈ [0.382, 1/2)` the
next is `u − 0.382 < 0.118` and the one after lies in `[0.618, 0.736)`
(`wy_gold_two_mul_even_iff`). -/
theorem goldCycleEvens_infinite : {n : ℤ | 0 < n ∧ n % 2 = 0 ∧ Wg n % 2 = 1}.Infinite := by
  have hg := gold_bounds
  have key : ∀ k : ℤ, ∃ i : ℤ, 0 ≤ i ∧ i ≤ 2 ∧ 1 / 2 ≤ Int.fract (((k + i : ℤ) : ℝ) * φ) := by
    intro k
    have hkF : (k : ℝ) * φ = ⌊(k : ℝ) * φ⌋ + Int.fract ((k : ℝ) * φ) :=
      (Int.floor_add_fract _).symm
    have hu0 := Int.fract_nonneg ((k : ℝ) * φ)
    have hu1 := Int.fract_lt_one ((k : ℝ) * φ)
    set u := Int.fract ((k : ℝ) * φ)
    rcases le_or_gt (1 / 2) u with h | h
    · exact ⟨0, le_rfl, by norm_num, by simpa using h⟩
    rcases lt_or_ge u (2 - φ) with h' | h'
    · refine ⟨1, by norm_num, by norm_num, ?_⟩
      have : Int.fract (((k + 1 : ℤ) : ℝ) * φ) = u + φ - 1 := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, ⌊(k : ℝ) * φ⌋ + 1, ?_⟩
        push_cast; linarith
      rw [this]; linarith
    · refine ⟨2, by norm_num, le_rfl, ?_⟩
      have : Int.fract (((k + 2 : ℤ) : ℝ) * φ) = u + 2 * φ - 3 := by
        rw [Int.fract_eq_iff]
        refine ⟨by linarith, by linarith, ⌊(k : ℝ) * φ⌋ + 3, ?_⟩
        push_cast; linarith
      rw [this]; linarith
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨i, hi0, hi2, hi⟩ := key (max N 0 + 1)
  have hmem : 2 * (max N 0 + 1 + i) ∈ {n : ℤ | 0 < n ∧ n % 2 = 0 ∧ Wg n % 2 = 1} := by
    refine ⟨by omega, by omega, ?_⟩
    have := (wy_gold_two_mul_even_iff (max N 0 + 1 + i)).not.2 (not_lt.2 hi)
    omega
  have := hN hmem
  omega

/-! ## The Sturmian trap `S′ = coneSet 3 (−1)` -/

/-- **(drafted, 99%).**  `S′ = {2k : k > 0, {kφ} < 1/2}` (`wy_gold_two_mul_even_iff`). -/
theorem mem_coneSet_gold_iff (n : ℤ) :
    n ∈ coneSet 3 (-1) ↔ ∃ k : ℤ, 0 < k ∧ n = 2 * k ∧ Int.fract ((k : ℝ) * φ) < 1 / 2 := by
  unfold coneSet
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h2, hW⟩
    have hn2 : n = 2 * (n / 2) := by omega
    rw [hn2] at hW
    exact ⟨n / 2, by omega, hn2, (wy_gold_two_mul_even_iff _).1 hW⟩
  · rintro ⟨k, hk, rfl, hu⟩
    exact ⟨by omega, by omega, (wy_gold_two_mul_even_iff _).2 hu⟩

/-- **(proved: an instance of Theorem K).**  `S′` is `W`-invariant. -/
theorem goldPerm_mapsTo_coneSet : ∀ n ∈ coneSet 3 (-1), goldPerm n ∈ coneSet 3 (-1) :=
  coneSet_trap _ _

/-- **(drafted, 98%; the Sturmian rotation).**  If `{kφ} < 1/2` then `W(2k) = 2k′` with
`k′ = k + ⌊kφ⌋` and `{k′φ} = {kφ}/φ²`; for every `k ∈ ℤ`.  Paper proof: module docstring
(`φ² = φ + 1`, `1/φ² = 2 − φ`, `Int.fract_eq_iff`). -/
theorem fract_gold_image {k : ℤ} (hk : Int.fract ((k : ℝ) * φ) < 1 / 2) :
    Wg (2 * k) = 2 * (k + ⌊(k : ℝ) * φ⌋) ∧
      Int.fract (((k + ⌊(k : ℝ) * φ⌋ : ℤ) : ℝ) * φ) = Int.fract ((k : ℝ) * φ) / φ ^ 2 := by
  have hg := gold_bounds
  have hsq := goldenRatio_sq
  have hkF : (k : ℝ) * φ = ⌊(k : ℝ) * φ⌋ + Int.fract ((k : ℝ) * φ) :=
    (Int.floor_add_fract _).symm
  have hu0 := Int.fract_nonneg ((k : ℝ) * φ)
  refine ⟨?_, ?_⟩
  · rw [wy_gold_two_mul, show 2 * (k : ℝ) * φ = 2 * ((k : ℝ) * φ) by ring,
      floor_two_mul_of_lt hk]
    ring
  · have hinv : 1 / φ ^ 2 = 2 - φ := by
      rw [div_eq_iff (by positivity)]; linear_combination (φ - 1) * hsq
    rw [div_eq_mul_one_div, hinv, Int.fract_eq_iff]
    refine ⟨mul_nonneg hu0 (by linarith), by nlinarith,
      2 * ⌊(k : ℝ) * φ⌋ + k, ?_⟩
    push_cast
    linear_combination (2 - φ) * hkF + (k : ℝ) * hsq

/-- **(drafted, 96%).**  `W(S′) = {2k′ : k′ > 0, {k′φ} < 1/(2φ²)}`.  Paper proof: `⊆` by
`fract_gold_image`; `⊇`: for `{k′φ} < 1/(2φ²)` put `k = ⌈k′/φ²⌉`; then `k′ = ⌊kφ²⌋ = k + ⌊kφ⌋`
(module docstring; `k′/φ² = 2k′ − k′φ`, so `{k′/φ²} = 1 − {k′φ} > 1 − 1/φ²`), `k ≥ 1`, and
`{kφ} = φ²{k′φ} < 1/2` (`fract_gold_image` read backward). -/
theorem mem_image_coneSet_gold_iff (n : ℤ) :
    n ∈ goldPerm '' coneSet 3 (-1) ↔
      ∃ k : ℤ, 0 < k ∧ n = 2 * k ∧ Int.fract ((k : ℝ) * φ) < 1 / (2 * φ ^ 2) := by
  have hg := gold_bounds
  have hsq := goldenRatio_sq
  have hφ2 : 0 < φ ^ 2 := by positivity
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨k, hk, rfl, hu⟩ := (mem_coneSet_gold_iff m).1 hm
    obtain ⟨h1, h2⟩ := fract_gold_image hu
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hF : 1 ≤ ⌊(k : ℝ) * φ⌋ := by rw [Int.le_floor]; push_cast; nlinarith
    refine ⟨k + ⌊(k : ℝ) * φ⌋, by omega, by rw [goldPerm_apply, h1], ?_⟩
    rw [h2, div_lt_div_iff₀ hφ2 (by positivity)]
    nlinarith
  · rintro ⟨k', hk', rfl, hv⟩
    have hkG : (k' : ℝ) * φ = ⌊(k' : ℝ) * φ⌋ + Int.fract ((k' : ℝ) * φ) :=
      (Int.floor_add_fract _).symm
    have hv0 := Int.fract_nonneg ((k' : ℝ) * φ)
    set G := ⌊(k' : ℝ) * φ⌋ with hG
    set v := Int.fract ((k' : ℝ) * φ) with hv_def
    have hv' : v * φ ^ 2 < 1 / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hv; linarith
    have hk'1 : (1 : ℝ) ≤ k' := by exact_mod_cast (by omega : 1 ≤ k')
    -- `k = 2k' − G`: `kφ = (G − k') + vφ²`
    have hkφ : ((2 * k' - G : ℤ) : ℝ) * φ = ((G - k' : ℤ) : ℝ) + v * φ ^ 2 := by
      push_cast
      linear_combination (φ + 1) * hkG - ((k' : ℝ) + v) * hsq
    have hfr : Int.fract (((2 * k' - G : ℤ) : ℝ) * φ) = v * φ ^ 2 := by
      rw [Int.fract_eq_iff]
      exact ⟨by positivity, by linarith, G - k', by rw [hkφ]; ring⟩
    have hfl : ⌊((2 * k' - G : ℤ) : ℝ) * φ⌋ = G - k' := by
      rw [hkφ, Int.floor_intCast_add, Int.floor_eq_zero_iff.2 ⟨by positivity, by linarith⟩]
      ring
    have hfr' : Int.fract (((2 * k' - G : ℤ) : ℝ) * φ) < 1 / 2 := by rw [hfr]; exact hv'
    have hGlt : G < 2 * k' := by
      have : (G : ℝ) < 2 * k' := by
        have := Int.floor_le ((k' : ℝ) * φ); rw [← hG] at this; nlinarith
      exact_mod_cast this
    refine ⟨2 * (2 * k' - G), (mem_coneSet_gold_iff _).2 ⟨2 * k' - G, by omega, rfl, hfr'⟩, ?_⟩
    rw [goldPerm_apply, (fract_gold_image hfr').1, hfl]
    ring

/-! ## Classification via Lemma P -/

/-- The exceptional set `Φ = {z | W³ z = z}`: in `ℕ⁺`, the fixed point `1` and the 3-cycles
(`mem_goldCycles_iff`). -/
def goldCycles : Set ℤ :=
  {z | Wg^[3] z = z}

theorem three_le_gold : 3 ≤ alphaK 3 (-1) := by
  rw [alphaK_three_neg_one_eq_gold]; linarith [gold_bounds.1]

theorem gold_one : Wg 1 = 1 := wy_one (by linarith [three_le_gold])

theorem gold_iter_two (n : ℤ) : Wg^[2] n = Wg (Wg n) := rfl

theorem goldPerm_pow_apply (j : ℕ) (x : ℤ) : (goldPerm ^ j) x = Wg^[j] x := by
  rw [Equiv.Perm.coe_pow]; rfl

theorem goldPerm_zpow_natCast (j : ℕ) (x : ℤ) : (goldPerm ^ (j : ℤ)) x = Wg^[j] x := by
  rw [zpow_natCast, goldPerm_pow_apply]

theorem mem_goldCycles_W {z : ℤ} (h : z ∈ goldCycles) : Wg z ∈ goldCycles := by
  show Wg (Wg (Wg (Wg z))) = Wg z
  have : Wg (Wg (Wg z)) = z := h
  rw [this]

theorem goldCycles_iff_W (z : ℤ) : goldPerm z ∈ goldCycles ↔ z ∈ goldCycles := by
  constructor
  · intro h
    have h' : Wg (Wg (Wg (Wg z))) = Wg z := h
    exact goldPerm.injective h'
  · exact mem_goldCycles_W

theorem lt_wy_gold_of_mem_coneSet {n : ℤ} (h : n ∈ coneSet 3 (-1)) : n < Wg n :=
  lt_wy_of_even three_le_gold h.1 h.2.1

/-- Points of the trap are off the cycles (`W` strictly increases on `S′`). -/
theorem not_mem_goldCycles_of_mem_coneSet {n : ℤ} (h : n ∈ coneSet 3 (-1)) :
    n ∉ goldCycles := by
  intro hc
  have h1 := goldPerm_mapsTo_coneSet n h
  have h2 := goldPerm_mapsTo_coneSet _ h1
  simp only [goldPerm_apply] at h1 h2
  have a := lt_wy_gold_of_mem_coneSet h
  have b := lt_wy_gold_of_mem_coneSet h1
  have c := lt_wy_gold_of_mem_coneSet h2
  have : Wg (Wg (Wg n)) = n := hc
  omega

/-- **(drafted, 97%).**  The positive points of `Φ` are `1` and the points of the 3-cycles
`{n, W n, W² n}`, `n > 0` even with `W n` odd.  Paper proof: `⊇` by `wy_one` and
`wy_gold_iterate_three` (`W³` commutes with `W`).  `⊆`: a positive cycle of length dividing `3`
other than `{1}` contains an even point (odd points `≥ 3` step down, `wy_lt_of_odd`); if
`W` of that even point were even, the orbit would enter the trap `S′`, where `W` strictly
increases (`lt_wy_of_even`), so it could not return. -/
theorem mem_goldCycles_iff {z : ℤ} (hz : 0 < z) :
    z ∈ goldCycles ↔ z = 1 ∨ ∃ n : ℤ, 0 < n ∧ n % 2 = 0 ∧ Wg n % 2 = 1 ∧
      (z = n ∨ z = Wg n ∨ z = Wg^[2] n) := by
  have hpos : ∀ y, 0 < Wg y ↔ 0 < y := fun y => wy_pos_iff (by linarith [three_le_gold]) y
  constructor
  · intro h
    have h3 : Wg (Wg (Wg z)) = z := h
    by_cases h1 : z = 1
    · exact Or.inl h1
    right
    have hW1 : Wg z ≠ 1 := fun e => h1 (goldPerm.injective (e.trans gold_one.symm))
    have hW2 : Wg (Wg z) ≠ 1 := fun e => hW1 (goldPerm.injective (e.trans gold_one.symm))
    -- an even point `e` of the cycle has `W e` odd (else it lies in the trap)
    have key : ∀ e, 0 < e → e % 2 = 0 → Wg (Wg (Wg e)) = e → Wg e % 2 = 1 := by
      intro e he0 he3 hc
      by_contra ho
      exact not_mem_goldCycles_of_mem_coneSet ⟨he0, he3, by omega⟩ hc
    have hz1 := (hpos z).2 hz
    have hz2 := (hpos _).2 hz1
    rcases Int.emod_two_eq_zero_or_one z with hze | hzo
    · exact ⟨z, hz, hze, key z hz hze h3, Or.inl rfl⟩
    rcases Int.emod_two_eq_zero_or_one (Wg z) with hwe | hwo
    · exact ⟨Wg z, hz1, hwe, key _ hz1 hwe (by rw [h3]), Or.inr (Or.inr h3.symm)⟩
    rcases Int.emod_two_eq_zero_or_one (Wg (Wg z)) with hve | hvo
    · exact ⟨Wg (Wg z), hz2, hve, key _ hz2 hve (by rw [h3]), Or.inr (Or.inl h3.symm)⟩
    · exfalso
      have a := wy_lt_of_odd three_le_gold (by omega) hzo
      have b := wy_lt_of_odd three_le_gold (by omega) hwo
      have c := wy_lt_of_odd three_le_gold (by omega) hvo
      rw [h3] at c
      omega
  · rintro (rfl | ⟨n, hn0, hn, hW, hx⟩)
    · show Wg (Wg (Wg 1)) = 1
      rw [gold_one, gold_one, gold_one]
    · have hn3 : n ∈ goldCycles := wy_gold_iterate_three hn hW
      rcases hx with rfl | rfl | rfl
      · exact hn3
      · exact mem_goldCycles_W hn3
      · exact mem_goldCycles_W (mem_goldCycles_W hn3)

theorem mem_orbit_of_iter (j : ℕ) {x y : ℤ} (h : Wg^[j] x = y) : y ∈ permOrbit goldPerm x :=
  ⟨(j : ℤ), by beta_reduce; rw [goldPerm_zpow_natCast]; exact h⟩

/-- The orbit of a point of the 3-cycle through `n` is the cycle. -/
theorem permOrbit_gold_cycle {n x : ℤ} (hn : n % 2 = 0) (hW : Wg n % 2 = 1)
    (hx : x = n ∨ x = Wg n ∨ x = Wg^[2] n) :
    permOrbit goldPerm x = {n, Wg n, Wg^[2] n} := by
  have h3 : Wg (Wg (Wg n)) = n := wy_gold_iterate_three hn hW
  have hC1 : ∀ y ∈ ({n, Wg n, Wg^[2] n} : Set ℤ),
      goldPerm y ∈ ({n, Wg n, Wg^[2] n} : Set ℤ) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, goldPerm_apply, gold_iter_two] at hy ⊢
    rcases hy with rfl | rfl | rfl
    · simp
    · simp
    · rw [h3]; simp
  have hC2 : ∀ y ∈ ({n, Wg n, Wg^[2] n} : Set ℤ),
      goldPerm.symm y ∈ ({n, Wg n, Wg^[2] n} : Set ℤ) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, gold_iter_two] at hy ⊢
    rcases hy with rfl | rfl | rfl
    · right; right; rw [Equiv.symm_apply_eq, goldPerm_apply, h3]
    · left; rw [Equiv.symm_apply_eq, goldPerm_apply]
    · right; left; rw [Equiv.symm_apply_eq, goldPerm_apply]
  have hxC : x ∈ ({n, Wg n, Wg^[2] n} : Set ℤ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact hx
  apply Set.Subset.antisymm
  · rintro y ⟨m, rfl⟩
    exact zpow_mem_of_closed goldPerm hC1 hC2 m x hxC
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact mem_orbit_of_iter 0 rfl
    · exact mem_orbit_of_iter 1 rfl
    · exact mem_orbit_of_iter 2 rfl
    · exact mem_orbit_of_iter 2 h3
    · exact mem_orbit_of_iter 0 rfl
    · exact mem_orbit_of_iter 1 rfl
    · exact mem_orbit_of_iter 1 h3
    · exact mem_orbit_of_iter 2 (by show Wg (Wg (Wg (Wg _))) = _; rw [h3])
    · exact mem_orbit_of_iter 0 rfl

/-- **(drafted, 97%).**  Lemma P applies with `S` = evens, `Φ = {z | W³ z = z}`, `T = 1`.  Paper
proof: `pos_iff` is `wy_pos_iff`; `mem_fix_iff`: `W³(W z) = W(W³ z)` and injectivity; (H1): a
positive odd `z ∉ Φ` has `z ≠ 1` (`wy_one`), so `W z < z` (`wy_lt_of_odd`); (H2) with `τ = 1`: a
positive even `s ∉ Φ` has `W s` even (else `W³ s = s`, `wy_gold_iterate_three`) and `W s > s`
(`lt_wy_of_even`). -/
theorem hyp_goldPerm : Hyp goldPerm {n | n % 2 = 0} goldCycles 1 := by
  refine ⟨fun n => wy_pos_iff (by linarith [three_le_gold]) n, goldCycles_iff_W, ?_, ?_⟩
  · intro z hz hS hΦ
    simp only [Set.mem_ofPred_eq] at hS
    rw [goldPerm_apply]
    have h1 : z ≠ 1 := by
      rintro rfl; apply hΦ; show Wg (Wg (Wg 1)) = 1; rw [gold_one, gold_one, gold_one]
    exact wy_lt_of_odd three_le_gold (by omega) (by omega)
  · intro s hs hs0 hsΦ
    simp only [Set.mem_ofPred_eq] at hs
    have hW : Wg s % 2 = 0 := by
      by_contra hc
      exact hsΦ (wy_gold_iterate_three hs (by omega))
    refine ⟨1, le_rfl, le_rfl, ?_, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, pow_one, goldPerm_apply]; exact hW
    · rw [pow_one, goldPerm_apply]; exact lt_wy_of_even three_le_gold hs0 hs
    · intro i h1 h2; omega

/-- **(drafted, 97%).**  For `x > 0`: the orbit is finite iff `x ∈ Φ`.  Paper proof: `x ∈ Φ`
gives an orbit inside `{x, W x, W² x}`; `x ∉ Φ` gives `permOrbit_infinite` (`hyp_goldPerm`). -/
theorem permOrbit_goldPerm_finite_iff {x : ℤ} (hx : 0 < x) :
    (permOrbit goldPerm x).Finite ↔ x ∈ goldCycles := by
  constructor
  · intro hfin
    by_contra hΦ
    exact permOrbit_infinite hyp_goldPerm hx hΦ hfin
  · intro h
    rcases (mem_goldCycles_iff hx).1 h with rfl | ⟨n, -, hn, hW, hxn⟩
    · rw [permOrbit_eq_singleton_of_fixed (σ := goldPerm) gold_one]
      exact Set.finite_singleton 1
    · rw [permOrbit_gold_cycle hn hW hxn]
      exact Set.toFinite _

/-- **(drafted, 97%; forward escape off the cycles).** -/
theorem tendsto_goldPerm_pow {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ goldCycles) :
    Tendsto (fun n : ℕ => (goldPerm ^ n) x) atTop atTop :=
  tendsto_pow hyp_goldPerm hx hxΦ

/-- **(drafted, 97%; backward escape off the cycles).** -/
theorem tendsto_goldPerm_pow_neg {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ goldCycles) :
    Tendsto (fun n : ℕ => (goldPerm ^ (-(n : ℤ))) x) atTop atTop :=
  tendsto_pow_neg hyp_goldPerm hx hxΦ

/-- **(drafted, 97%).**  An orbit through a positive point off `Φ` meets the trap `S′`.  Paper
proof: its minimum `y` (`exists_isOrbitMin`) is even (`isOrbitMin_iff`) and off `Φ`, so `W y` is
even (`hyp_goldPerm`'s (H2) argument): `y ∈ S′`. -/
theorem exists_mem_orbit_mem_coneSet_gold {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ goldCycles) :
    ∃ y ∈ permOrbit goldPerm x, y ∈ coneSet 3 (-1) := by
  obtain ⟨y, hy, hmin⟩ := exists_isOrbitMin hyp_goldPerm hx hxΦ
  have hy0 : 0 < y := permOrbit_subset_pos hyp_goldPerm hx hy
  have hyΦ : y ∉ goldCycles := permOrbit_subset_compl hyp_goldPerm hxΦ hy
  have hye := ((isOrbitMin_iff hyp_goldPerm hy0 hyΦ).1 hmin).1
  simp only [Set.mem_ofPred_eq] at hye
  refine ⟨y, hy, hy0, hye, ?_⟩
  by_contra hc
  exact hyΦ (wy_gold_iterate_three hye (by omega))

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
  by_cases hΦ : x ∈ goldCycles
  · rcases (mem_goldCycles_iff hx).1 hΦ with rfl | ⟨n, hn0, hn, hW, hxn⟩
    · left; exact permOrbit_eq_singleton_of_fixed (σ := goldPerm) gold_one
    · right; left; exact ⟨n, hn0, hn, hW, permOrbit_gold_cycle hn hW hxn⟩
  · right; right
    exact ⟨permOrbit_infinite hyp_goldPerm hx hΦ, tendsto_goldPerm_pow hx hΦ,
      tendsto_goldPerm_pow_neg hx hΦ, exists_mem_orbit_mem_coneSet_gold hx hΦ⟩

/-- **(drafted, 97%; Lemma P minimum test, `T = 1`).**  For `x > 0` off `Φ`: `x` is the minimum
of its orbit iff `x` is even and `W⁻¹(x)` is odd (`isOrbitMin_iff`, `zpow_neg_one`). -/
theorem isOrbitMin_goldPerm_iff_pred {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ goldCycles) :
    IsOrbitMin goldPerm x ↔ x % 2 = 0 ∧ goldPerm.symm x % 2 = 1 := by
  rw [isOrbitMin_iff hyp_goldPerm hx hxΦ]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := h2 1 le_rfl le_rfl
    rw [Nat.cast_one, zpow_neg_one, Equiv.Perm.inv_def] at this
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i hi1 hi2 => ?_⟩
    obtain rfl : i = 1 := by omega
    rw [Nat.cast_one, zpow_neg_one, Equiv.Perm.inv_def]
    omega

theorem gold_thresh_lt : 1 / (2 * φ ^ 2) < 1 / 2 := by
  have hg := gold_bounds
  exact one_div_lt_one_div_of_lt (by norm_num) (by nlinarith)

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
  constructor
  · rintro ⟨hmin, hinf⟩
    have hΦ : x ∉ goldCycles := fun h => hinf ((permOrbit_goldPerm_finite_iff hx).2 h)
    obtain ⟨he, hs⟩ := (isOrbitMin_goldPerm_iff_pred hx hΦ).1 hmin
    have hW : Wg x % 2 = 0 := by
      by_contra hc; exact hΦ (wy_gold_iterate_three he (by omega))
    obtain ⟨k, hk, rfl, hu⟩ := (mem_coneSet_gold_iff x).1 ⟨hx, he, hW⟩
    refine ⟨k, rfl, ?_, hu⟩
    by_contra hc
    obtain ⟨y, hy, hyx⟩ := (mem_image_coneSet_gold_iff (2 * k)).2 ⟨k, hk, rfl, not_le.1 hc⟩
    have : goldPerm.symm (2 * k) = y := by rw [← hyx]; simp
    rw [this] at hs
    have := hy.2.1
    omega
  · rintro ⟨k, rfl, h1, h2⟩
    have hk : 0 < k := by omega
    have hcone : 2 * k ∈ coneSet 3 (-1) := (mem_coneSet_gold_iff _).2 ⟨k, hk, rfl, h2⟩
    have hΦ := not_mem_goldCycles_of_mem_coneSet hcone
    refine ⟨(isOrbitMin_goldPerm_iff_pred hx hΦ).2 ⟨by omega, ?_⟩,
      fun hfin => hΦ ((permOrbit_goldPerm_finite_iff hx).1 hfin)⟩
    by_contra hc
    have hyx : goldPerm (goldPerm.symm (2 * k)) = 2 * k := by simp
    have hy0 : 0 < goldPerm.symm (2 * k) := (hyp_goldPerm.pos_iff _).1 (by rw [hyx]; omega)
    have hycone : goldPerm.symm (2 * k) ∈ coneSet 3 (-1) :=
      ⟨hy0, by omega, by show Wg _ % 2 = 0; rw [← goldPerm_apply, hyx]; omega⟩
    obtain ⟨k', hk', hkk, hv⟩ := (mem_image_coneSet_gold_iff (2 * k)).1 ⟨_, hycone, hyx⟩
    obtain rfl : k' = k := by omega
    linarith

/-- **(drafted, 97%; finite-orbit minima).**  For `x > 0`: `x` is the minimum of a finite orbit
iff `x = 1` or `x = 2k` with `{kφ} ≥ 1/2` (`mem_goldCycles_iff`, `isOrbitMin_of_cycle_gold`,
`wy_gold_two_mul_even_iff`; the odd points of a 3-cycle exceed its even point). -/
theorem isOrbitMin_and_finite_iff {x : ℤ} (hx : 0 < x) :
    IsOrbitMin goldPerm x ∧ (permOrbit goldPerm x).Finite ↔
      x = 1 ∨ ∃ k : ℤ, x = 2 * k ∧ 1 / 2 ≤ Int.fract ((k : ℝ) * φ) := by
  constructor
  · rintro ⟨hmin, hfin⟩
    have hΦ := (permOrbit_goldPerm_finite_iff hx).1 hfin
    rcases (mem_goldCycles_iff hx).1 hΦ with rfl | ⟨n, hn0, hn, hW, hxn⟩
    · exact Or.inl rfl
    right
    have hnx : n ∈ permOrbit goldPerm x := by rw [permOrbit_gold_cycle hn hW hxn]; simp
    have hxn' : x ∈ permOrbit goldPerm n := by
      rw [permOrbit_gold_cycle hn hW (Or.inl rfl)]
      rcases hxn with h | h | h <;> simp [h]
    have hxeq : x = n := le_antisymm (hmin n hnx) (isOrbitMin_of_cycle_gold hn0 hn hW x hxn')
    subst hxeq
    exact ⟨x / 2, by omega, fract_ge_of_odd hn hW⟩
  · rintro (rfl | ⟨k, rfl, hu⟩)
    · refine ⟨isOrbitMin_of_fixed (σ := goldPerm) gold_one, ?_⟩
      rw [permOrbit_eq_singleton_of_fixed (σ := goldPerm) gold_one]
      exact Set.finite_singleton 1
    · have hW : Wg (2 * k) % 2 = 1 := by
        have := (wy_gold_two_mul_even_iff k).not.2 (not_lt.2 hu); omega
      have hn : (2 * k) % 2 = 0 := by omega
      refine ⟨isOrbitMin_of_cycle_gold hx hn hW, ?_⟩
      rw [permOrbit_gold_cycle hn hW (Or.inl rfl)]
      exact Set.toFinite _

/-- **(drafted, 96%; all minima).**  For `x > 0`: `x` is an orbit minimum iff `x = 1` or `x = 2k`
with `{kφ} ≥ 1/(2φ²)` (`isOrbitMin_and_infinite_iff`, `isOrbitMin_and_finite_iff`). -/
theorem isOrbitMin_goldPerm_iff {x : ℤ} (hx : 0 < x) :
    IsOrbitMin goldPerm x ↔
      x = 1 ∨ ∃ k : ℤ, x = 2 * k ∧ 1 / (2 * φ ^ 2) ≤ Int.fract ((k : ℝ) * φ) := by
  have hlt := gold_thresh_lt
  constructor
  · intro hmin
    rcases (permOrbit goldPerm x).finite_or_infinite with hf | hi
    · rcases (isOrbitMin_and_finite_iff hx).1 ⟨hmin, hf⟩ with h | ⟨k, rfl, hu⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, rfl, by linarith⟩
    · obtain ⟨k, rfl, h1, -⟩ := (isOrbitMin_and_infinite_iff hx).1 ⟨hmin, hi⟩
      exact Or.inr ⟨k, rfl, h1⟩
  · rintro (rfl | ⟨k, rfl, hu⟩)
    · exact isOrbitMin_of_fixed (σ := goldPerm) gold_one
    · rcases lt_or_ge (Int.fract ((k : ℝ) * φ)) (1 / 2) with h | h
      · exact ((isOrbitMin_and_infinite_iff hx).2 ⟨k, rfl, hu, h⟩).1
      · exact ((isOrbitMin_and_finite_iff hx).2 (Or.inr ⟨k, rfl, h⟩)).1

/-- **(drafted, 96%; the infinite-orbit minima are Theorem K's entry points).**  `S′ ∖ W(S′)` is
exactly the set of positive minima of infinite orbits, so every infinite orbit enters the trap
at its minimum, and K's entry density `(1/4)(1 − 2/α) = 1/(4φ)` is attained.  Paper proof:
`mem_coneSet_gold_iff`, `mem_image_coneSet_gold_iff`, `isOrbitMin_and_infinite_iff`. -/
theorem mem_coneEntry_gold_iff (x : ℤ) :
    x ∈ coneSet 3 (-1) \ goldPerm '' coneSet 3 (-1) ↔
      0 < x ∧ IsOrbitMin goldPerm x ∧ (permOrbit goldPerm x).Infinite := by
  constructor
  · rintro ⟨hc, hni⟩
    obtain ⟨k, hk, rfl, hu⟩ := (mem_coneSet_gold_iff _).1 hc
    have hx : 0 < 2 * k := by omega
    refine ⟨hx, (isOrbitMin_and_infinite_iff hx).2 ⟨k, rfl, ?_, hu⟩⟩
    by_contra h
    exact hni ((mem_image_coneSet_gold_iff _).2 ⟨k, hk, rfl, not_le.1 h⟩)
  · rintro ⟨hx, hmi⟩
    obtain ⟨k, rfl, h1, h2⟩ := (isOrbitMin_and_infinite_iff hx).1 hmi
    refine ⟨(mem_coneSet_gold_iff _).2 ⟨k, by omega, rfl, h2⟩, fun hi => ?_⟩
    obtain ⟨k', -, hkk, hv⟩ := (mem_image_coneSet_gold_iff _).1 hi
    obtain rfl : k' = k := by omega
    linarith

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
  unfold minCount
  have hset : ((Finset.Icc (1 : ℤ) X).filter fun x => IsOrbitMin goldPerm x) =
      insert 1 (((Finset.Icc (1 : ℤ) ((X / 2 : ℕ) : ℤ)).filter
        fun k : ℤ => 1 / (2 * φ ^ 2) ≤ Int.fract ((k : ℝ) * φ)).image fun k => 2 * k) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, hm⟩
      rcases (isOrbitMin_goldPerm_iff (by omega)).1 hm with h | ⟨k, rfl, hu⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, ⟨⟨by omega, by omega⟩, hu⟩, rfl⟩
    · rintro (rfl | ⟨k, ⟨⟨h1, h2⟩, hu⟩, rfl⟩)
      · exact ⟨⟨le_rfl, by exact_mod_cast hX⟩, (isOrbitMin_goldPerm_iff one_pos).2 (Or.inl rfl)⟩
      · exact ⟨⟨by omega, by omega⟩,
          (isOrbitMin_goldPerm_iff (by omega)).2 (Or.inr ⟨k, rfl, hu⟩)⟩
  rw [hset, Finset.card_insert_of_notMem, Finset.card_image_of_injective _ (fun a b h => by
    have : 2 * a = 2 * b := h; omega)]
  · omega
  · simp only [Finset.mem_image]; rintro ⟨k, -, hk⟩; omega

/-- Counting even orbit points `2k ∈ [1, X]` by `k ∈ [1, ⌊X/2⌋] ⊆ ℕ`. -/
theorem card_two_mul (X : ℕ) (Q : ℤ → Prop) [DecidablePred Q] (P : ℝ → Prop)
    [DecidablePred fun k : ℕ => P (k : ℝ)]
    (hQ : ∀ x : ℤ, 0 < x → (Q x ↔ ∃ k : ℤ, x = 2 * k ∧ P (k : ℝ))) :
    ((Finset.Icc (1 : ℤ) X).filter Q).card =
      ((Finset.Icc 1 (X / 2)).filter fun k : ℕ => P (k : ℝ)).card := by
  have hset : ((Finset.Icc (1 : ℤ) X).filter Q) =
      ((Finset.Icc 1 (X / 2)).filter fun k : ℕ => P (k : ℝ)).image
        fun k : ℕ => 2 * (k : ℤ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, hq⟩
      obtain ⟨k, rfl, hk⟩ := (hQ _ (by omega)).1 hq
      refine ⟨k.toNat, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      have : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      rw [this]; exact hk
    · rintro ⟨k, ⟨⟨h1, h2⟩, hk⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, (hQ _ (by omega)).2 ⟨k, rfl, by rw [Int.cast_natCast]; exact hk⟩⟩
  rw [hset, Finset.card_image_of_injective _ (fun a b h => by
    have : 2 * (a : ℤ) = 2 * (b : ℤ) := h; omega)]

/-- As `card_two_mul`, with the extra point `1`. -/
theorem card_one_two_mul {X : ℕ} (hX : 1 ≤ X) (Q : ℤ → Prop) [DecidablePred Q] (P : ℝ → Prop)
    [DecidablePred fun k : ℕ => P (k : ℝ)]
    (hQ : ∀ x : ℤ, 0 < x → (Q x ↔ x = 1 ∨ ∃ k : ℤ, x = 2 * k ∧ P (k : ℝ))) :
    ((Finset.Icc (1 : ℤ) X).filter Q).card =
      1 + ((Finset.Icc 1 (X / 2)).filter fun k : ℕ => P (k : ℝ)).card := by
  have hsplit : (Finset.Icc (1 : ℤ) X).filter Q =
      insert 1 ((Finset.Icc (1 : ℤ) X).filter fun x => Q x ∧ x ≠ 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨h1, h2⟩, hq⟩
      by_cases hx : x = 1
      · exact Or.inl hx
      · exact Or.inr ⟨⟨h1, h2⟩, hq, hx⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, hq, -⟩)
      · exact ⟨⟨le_rfl, by exact_mod_cast hX⟩, (hQ 1 one_pos).2 (Or.inl rfl)⟩
      · exact ⟨⟨h1, h2⟩, hq⟩
  rw [hsplit, Finset.card_insert_of_notMem (by simp), card_two_mul X _ P ?_, add_comm]
  intro x hx
  rw [hQ x hx]
  constructor
  · rintro ⟨h | h, hne⟩
    · exact absurd h hne
    · exact h
  · rintro ⟨k, rfl, hk⟩
    exact ⟨Or.inr ⟨k, rfl, hk⟩, by omega⟩

/-- A frequency `A(N)/N → c` along `N = ⌊X/2⌋` gives density `c/2` in `X`. -/
theorem tendsto_count_half {A : ℕ → ℕ} {c : ℝ} (m : ℕ)
    (hA : Tendsto (fun N : ℕ => (A N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun X : ℕ => ((m + A (X / 2) : ℕ) : ℝ) / X) atTop (𝓝 (c / 2)) := by
  have hN : Tendsto (fun X : ℕ => X / 2) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun X hX => by omega⟩
  have h1 := hA.comp hN
  have h2 : Tendsto (fun X : ℕ => ((X / 2 : ℕ) : ℝ) / X) atTop (𝓝 (1 / 2)) := by
    have hlo : Tendsto (fun X : ℕ => 1 / 2 - (1 / 2 : ℝ) / X) atTop (𝓝 (1 / 2)) := by
      simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with X hX
      have hX' : (0 : ℝ) < X := by exact_mod_cast hX
      have : (X : ℝ) ≤ 2 * ((X / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (by omega : X ≤ 2 * (X / 2) + 1)
      rw [sub_div' hX'.ne', div_le_div_iff_of_pos_right hX']
      linarith
    · filter_upwards [eventually_ge_atTop 1] with X hX
      have hX' : (0 : ℝ) < X := by exact_mod_cast hX
      have : 2 * ((X / 2 : ℕ) : ℝ) ≤ X := by exact_mod_cast (by omega : 2 * (X / 2) ≤ X)
      rw [div_le_iff₀ hX']
      linarith
  have h3 : Tendsto (fun X : ℕ => (m : ℝ) / X) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)
  have h4 := h3.add (h1.mul h2)
  rw [show c / 2 = 0 + c * (1 / 2) by ring]
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hX2 : (0 : ℝ) < ((X / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < X / 2)
  have hX' : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  simp only [Function.comp, Nat.cast_add]
  field_simp

/-- **(drafted, 95%; 3-cycle density, conditional).**  Assuming one-dimensional Weyl
equidistribution (a literature hypothesis), the 3-cycle minima have density `1/4`.  Paper proof:
`isOrbitMin_and_finite_iff`: the count is `1 + #{k ≤ X/2 : {kφ} ∈ [1/2, 1)}`;
`WeylEquidistribution` with `θ = φ` (`goldenRatio_irrational`), `[a, b) = [1/2, 1)`, at
`N = ⌊X/2⌋`. -/
theorem tendsto_goldCycleMinCount (hW : WeylEquidistribution) :
    Tendsto (fun X : ℕ => (goldCycleMinCount X : ℝ) / X) atTop (𝓝 (1 / 4)) := by
  have hW1 := hW φ goldenRatio_irrational (1 / 2) 1 (by norm_num) (by norm_num) le_rfl
  have h := tendsto_count_half 1 hW1
  rw [show (1 : ℝ) / 4 = (1 - 1 / 2) / 2 by norm_num]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  classical
  unfold goldCycleMinCount
  have hQ : ∀ x : ℤ, 0 < x → ((IsOrbitMin goldPerm x ∧ (permOrbit goldPerm x).Finite) ↔
      x = 1 ∨ ∃ k : ℤ, x = 2 * k ∧ Int.fract ((k : ℝ) * φ) ∈ Set.Ico (1 / 2 : ℝ) 1) := by
    intro x hx
    rw [isOrbitMin_and_finite_iff hx]
    simp only [Set.mem_Ico, Int.fract_lt_one, and_true]
  rw [card_one_two_mul hX _ (fun r : ℝ => Int.fract (r * φ) ∈ Set.Ico (1 / 2 : ℝ) 1) hQ]

/-- **(drafted, 95%; infinite-orbit minima density, conditional).**  Assuming one-dimensional
Weyl equidistribution, the infinite-orbit minima have density `1/(4φ)`.  Paper proof:
`isOrbitMin_and_infinite_iff`, `WeylEquidistribution` with `[a, b) = [1/(2φ²), 1/2)`, of length
`(φ² − 1)/(2φ²) = 1/(2φ)`, at `N = ⌊X/2⌋`. -/
theorem tendsto_goldInfMinCount (hW : WeylEquidistribution) :
    Tendsto (fun X : ℕ => (goldInfMinCount X : ℝ) / X) atTop (𝓝 (1 / (4 * φ))) := by
  have hg := gold_bounds
  have hlt := gold_thresh_lt
  have hW1 := hW φ goldenRatio_irrational (1 / (2 * φ ^ 2)) (1 / 2) (by positivity) hlt.le
    (by norm_num)
  have h := tendsto_count_half 0 hW1
  rw [show 1 / (4 * φ) = (1 / 2 - 1 / (2 * φ ^ 2)) / 2 by
    have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    field_simp; linear_combination (-2 : ℝ) * goldenRatio_sq + (-7 / 2 : ℝ) * h5]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  classical
  unfold goldInfMinCount
  have hQ : ∀ x : ℤ, 0 < x → ((IsOrbitMin goldPerm x ∧ (permOrbit goldPerm x).Infinite) ↔
      ∃ k : ℤ, x = 2 * k ∧ Int.fract ((k : ℝ) * φ) ∈ Set.Ico (1 / (2 * φ ^ 2)) (1 / 2)) := by
    intro x hx
    rw [isOrbitMin_and_infinite_iff hx]
    simp only [Set.mem_Ico]
  rw [card_two_mul X _ (fun r : ℝ => Int.fract (r * φ) ∈ Set.Ico (1 / (2 * φ ^ 2)) (1 / 2)) hQ]
  try simp

/-- **(drafted, 95%; total minima density, conditional).**  `1/4 + 1/(4φ) = 1/2 − 1/(4φ²)`
(`minCount = goldCycleMinCount + goldInfMinCount`, or directly from `minCount_goldPerm_eq`). -/
theorem tendsto_minCount_goldPerm (hW : WeylEquidistribution) :
    Tendsto (fun X : ℕ => (minCount goldPerm X : ℝ) / X) atTop (𝓝 (1 / 4 + 1 / (4 * φ))) := by
  have hg := gold_bounds
  have hlt := gold_thresh_lt
  have hW1 := hW φ goldenRatio_irrational (1 / (2 * φ ^ 2)) 1 (by positivity) (by linarith)
    le_rfl
  have h := tendsto_count_half 1 hW1
  rw [show 1 / 4 + 1 / (4 * φ) = (1 - 1 / (2 * φ ^ 2)) / 2 by
    have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    field_simp; linear_combination (-4 : ℝ) * goldenRatio_sq + (-1 : ℝ) * h5]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  classical
  unfold minCount
  have hQ : ∀ x : ℤ, 0 < x → (IsOrbitMin goldPerm x ↔
      x = 1 ∨ ∃ k : ℤ, x = 2 * k ∧ Int.fract ((k : ℝ) * φ) ∈ Set.Ico (1 / (2 * φ ^ 2)) 1) := by
    intro x hx
    rw [isOrbitMin_goldPerm_iff hx]
    simp only [Set.mem_Ico, Int.fract_lt_one, and_true]
  rw [card_one_two_mul hX _ (fun r : ℝ => Int.fract (r * φ) ∈ Set.Ico (1 / (2 * φ ^ 2)) 1) hQ]

end CollatzMoonshot.WythoffGolden
