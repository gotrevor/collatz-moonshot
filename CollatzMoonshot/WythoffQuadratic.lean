/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.AmusicalTrap

/-!
# Theorem F: the quadratic Wythoff members `α = 2r + 2√(r² − r)` are solved

The Wythoff (Beatty-merge) family `W_α(2k) = ⌊kα⌋`, `W_α(2k−1) = ⌊kβ⌋`, `1/α + 1/β = 1`,
passes through `U` at `α = 3` (research note `wythoff`).  For an integer `r ≥ 2` take
`α = 2r + 2√(r² − r)` and its Galois conjugate `β = 2r − 2√(r² − r) ∈ (1, 6/5)`, so
`α + β = αβ = 4r` (research note `wythoff-2sqrtm`, §4).  Write `m = r² − r` (never a square).

**Definitions.**  `⌊2k√m⌋` is `Nat.sqrt (4k²m)` for `k ≥ 0` and `−Nat.sqrt (4k²m) − 1` for
`k < 0` (`sfl`).  Then `⌊kα⌋ = 2rk + ⌊2k√m⌋` and `⌈kβ⌉ − 1 = 2rk − ⌊2k√m⌋ − 1`, and `wq` is the
merge on all of `ℤ`: `2k ↦ ⌊kα⌋`, `2k − 1 ↦ ⌈kβ⌉ − 1` (`= ⌊kβ⌋` for `k ≠ 0`).  With the ceiling
on the odd branch it is a permutation of `ℤ` (Rayleigh, `compl_beattySeq`) preserving `ℕ⁺`, so
`AmusicalTrap`'s orbit notions apply verbatim.  The partner `wqp` (`α ↔ β`) is
`2k ↦ ⌈kβ⌉ − 1`, `2k − 1 ↦ ⌊kα⌋`, i.e. `wq` precomposed with `2k ↔ 2k − 1`.

1. **Theorem D (EO identity).**  If `W(2k)` is odd then `W(W(2k)) = 2rk`.  Partner: if
   `W'(2k − 1)` is even then `W'(W'(2k − 1)) = 2rk − 1`.
2. **Steps.**  `W(1) = 1`; `W(2k) > 2k` for `k ≥ 1`; `W(2j − 1) < 2j − 1` for `j ≥ 2`.
3. **Theorem F (classification).**  `{1}` is the only finite orbit in `ℕ⁺`; every other orbit
   tends to `∞` in both time directions; its minimum is its unique *entry point*: the even `y`
   whose two predecessors are odd, equivalently `y ∈ W(odd)` and `y ≠ 2rk` with `W(2k)` odd.
   So `W` has infinitely many infinite orbits.  The partner has no finite orbit in `ℕ⁺`, and its
   orbit minima are the odd `y` whose two predecessors are even.
4. **Count.**  `#{orbit minima ≤ X} = 1 + A(X) − B(X)` exactly, with
   `A(X) = #{j ≥ 1 : ⌊jβ⌋ ≤ X even}`, `B(X) = #{k ≥ 1 : 2rk ≤ X, ⌊kα⌋ odd}`; unconditional
   linear bounds; and, from the equidistribution of `k√m` mod 1 (a named literature hypothesis,
   not in Mathlib), the density `d_r = (r − 1 + √(r² − r))/(4r)`.  Partner: `A′(X) − B′(X)`, same
   `d_r`.  The `O(log X)` error term (Ostrowski discrepancy for a quadratic irrational) is not
   stated.
-/

namespace CollatzMoonshot.WythoffQuadratic

open CollatzMoonshot.AmusicalTrap (permOrbit InfinitelyManyInfiniteOrbits
  infinitelyManyInfiniteOrbits_of_trap)
open Filter Topology

/-! ## The maps -/

/-- `⌊2|k|√(r² − r)⌋ = Nat.sqrt (4k²(r² − r))`. -/
def sqrtPart (r : ℕ) (k : ℤ) : ℕ :=
  Nat.sqrt (4 * k.natAbs ^ 2 * (r ^ 2 - r))

/-- `⌊2k√(r² − r)⌋` on all of `ℤ`.  For `r ≥ 2`, `r² − r` is not a square, so for `k < 0` the
floor is `−⌈2|k|√(r² − r)⌉ = −sqrtPart r k − 1` (`sfl_eq_floor`). -/
def sfl (r : ℕ) (k : ℤ) : ℤ :=
  if 0 ≤ k then (sqrtPart r k : ℤ) else -(sqrtPart r k : ℤ) - 1

/-- `W_α` on `ℤ`, `α = 2r + 2√(r² − r)`: `2k ↦ ⌊kα⌋ = 2rk + ⌊2k√(r² − r)⌋` and
`2k − 1 ↦ ⌈kβ⌉ − 1 = 2rk − ⌊2k√(r² − r)⌋ − 1`. -/
def wq (r : ℕ) (n : ℤ) : ℤ :=
  if n % 2 = 0 then r * n + sfl r (n / 2) else r * (n + 1) - sfl r ((n + 1) / 2) - 1

/-- The partner `W_β` on `ℤ`: `2k ↦ ⌈kβ⌉ − 1`, `2k − 1 ↦ ⌊kα⌋`. -/
def wqp (r : ℕ) (n : ℤ) : ℤ :=
  if n % 2 = 0 then r * n - sfl r (n / 2) - 1 else r * (n + 1) + sfl r ((n + 1) / 2)

/-- `α_r = 2r + 2√(r² − r)`. -/
noncomputable def alphaQ (r : ℕ) : ℝ :=
  2 * r + 2 * √((r : ℝ) ^ 2 - r)

/-- `β_r = 2r − 2√(r² − r) = α_r/(α_r − 1)`. -/
noncomputable def betaQ (r : ℕ) : ℝ :=
  2 * r - 2 * √((r : ℝ) ^ 2 - r)

/-! ## Branch formulas and the real bridge -/

section Bridge

variable {r : ℕ}

/-- **(ratified).**  Even branch. -/
theorem wq_two_mul (r : ℕ) (k : ℤ) : wq r (2 * k) = 2 * r * k + sfl r k := by
  sorry

/-- **(ratified).**  Odd branch. -/
theorem wq_two_mul_sub_one (r : ℕ) (k : ℤ) : wq r (2 * k - 1) = 2 * r * k - sfl r k - 1 := by
  sorry

/-- **(ratified).**  Partner, even branch. -/
theorem wqp_two_mul (r : ℕ) (k : ℤ) : wqp r (2 * k) = 2 * r * k - sfl r k - 1 := by
  sorry

/-- **(ratified).**  Partner, odd branch. -/
theorem wqp_two_mul_sub_one (r : ℕ) (k : ℤ) : wqp r (2 * k - 1) = 2 * r * k + sfl r k := by
  sorry

/-- **(ratified).**  The partner is `wq` precomposed with the involution `2k ↔ 2k − 1`. -/
theorem wqp_eq_wq (r : ℕ) (n : ℤ) : wqp r n = wq r (if n % 2 = 0 then n - 1 else n + 1) := by
  sorry

/-- **(ratified).**  `√(r² − r)` is irrational for `r ≥ 2`: `(r − 1)² < r² − r < r²`. -/
theorem irrational_sqrt (hr : 2 ≤ r) : Irrational √((r : ℝ) ^ 2 - r) := by
  sorry

/-- **(ratified).**  `α + β = 4r`. -/
theorem alphaQ_add_betaQ (r : ℕ) : alphaQ r + betaQ r = 4 * r := by
  sorry

/-- **(ratified).**  `αβ = 4r`. -/
theorem alphaQ_mul_betaQ (r : ℕ) : alphaQ r * betaQ r = 4 * r := by
  sorry

/-- **(ratified).**  `1 < β < 6/5` for `r ≥ 2`.  Paper proof: `β = 2r/(r + √(r² − r))`;
`β > 1 ⇔ √(r² − r) < r`, and `β < 6/5 ⇔ √(r² − r) > 2r/3 ⇔ 5r² > 9r`.  (At `r = 2`,
`β = 4 − 2√2 ≈ 1.1716`.) -/
theorem one_lt_betaQ_lt (hr : 2 ≤ r) : 1 < betaQ r ∧ betaQ r < 6 / 5 := by
  sorry

/-- **(ratified).**  `α` and `β` are Hölder conjugate: `1/α + 1/β = (α + β)/(αβ) = 1`. -/
theorem alphaQ_holderConjugate (hr : 2 ≤ r) : (alphaQ r).HolderConjugate (betaQ r) := by
  sorry

/-- **(ratified).**  `sfl` is the real floor.  Paper proof: `k ≥ 0` is `Nat.sqrt`'s spec
(`Real.nat_sqrt_le_real_sqrt`, `Real.real_sqrt_lt_nat_sqrt_succ`); for `k < 0`, the value
`2|k|√(r² − r)` is irrational, so `⌊−y⌋ = −⌊y⌋ − 1`. -/
theorem sfl_eq_floor (hr : 2 ≤ r) (k : ℤ) :
    sfl r k = ⌊(2 * k : ℝ) * √((r : ℝ) ^ 2 - r)⌋ := by
  sorry

/-- **(ratified).**  `W(2k) = ⌊kα⌋` for every `k ∈ ℤ`. -/
theorem wq_two_mul_eq_floor (hr : 2 ≤ r) (k : ℤ) : wq r (2 * k) = ⌊(k : ℝ) * alphaQ r⌋ := by
  sorry

/-- **(ratified).**  `W(2k − 1) = ⌈kβ⌉ − 1` for every `k ∈ ℤ` (Mathlib's `beattySeq'`). -/
theorem wq_two_mul_sub_one_eq_ceil (hr : 2 ≤ r) (k : ℤ) :
    wq r (2 * k - 1) = ⌈(k : ℝ) * betaQ r⌉ - 1 := by
  sorry

/-- **(ratified).**  `W(2k − 1) = ⌊kβ⌋` for `k ≠ 0` (`kβ` is irrational). -/
theorem wq_two_mul_sub_one_eq_floor (hr : 2 ≤ r) {k : ℤ} (hk : k ≠ 0) :
    wq r (2 * k - 1) = ⌊(k : ℝ) * betaQ r⌋ := by
  sorry

/-- **(ratified).**  Partner: `W'(2k) = ⌊kβ⌋` for `k ≠ 0`. -/
theorem wqp_two_mul_eq_floor (hr : 2 ≤ r) {k : ℤ} (hk : k ≠ 0) :
    wqp r (2 * k) = ⌊(k : ℝ) * betaQ r⌋ := by
  sorry

/-- **(ratified).**  Partner: `W'(2k − 1) = ⌊kα⌋`. -/
theorem wqp_two_mul_sub_one_eq_floor (hr : 2 ≤ r) (k : ℤ) :
    wqp r (2 * k - 1) = ⌊(k : ℝ) * alphaQ r⌋ := by
  sorry

end Bridge

/-! ## Bijectivity -/

section Bijection

variable {r : ℕ}

/-- **(ratified).**  `W` is a bijection of `ℤ`.  Paper proof: the even branch is
`k ↦ beattySeq α k`, the odd branch `k ↦ beattySeq' β k` (`wq_two_mul_eq_floor`,
`wq_two_mul_sub_one_eq_ceil`), both strictly increasing (`α, β > 1`), with complementary ranges
(`compl_beattySeq` with `alphaQ_holderConjugate`). -/
theorem wq_bijective (hr : 2 ≤ r) : Function.Bijective (wq r) := by
  sorry

/-- `W_α` as a permutation of `ℤ`. -/
noncomputable def wqPerm (r : ℕ) (hr : 2 ≤ r) : Equiv.Perm ℤ :=
  Equiv.ofBijective (wq r) (wq_bijective hr)

theorem wqPerm_apply (hr : 2 ≤ r) (n : ℤ) : wqPerm r hr n = wq r n := rfl

/-- **(ratified).**  `W` preserves `ℕ⁺` (and hence `ℤ≤0`).  Paper proof: for `k ≥ 1`,
`⌊kα⌋ ≥ 1` and `⌊kβ⌋ ≥ 1`; for `k ≤ 0`, `⌊kα⌋ ≤ 0` and `⌈kβ⌉ − 1 ≤ −1`. -/
theorem wq_pos_iff (hr : 2 ≤ r) (n : ℤ) : 0 < wq r n ↔ 0 < n := by
  sorry

/-- **(ratified).**  The partner is a bijection of `ℤ` (`wqp_eq_wq`). -/
theorem wqp_bijective (hr : 2 ≤ r) : Function.Bijective (wqp r) := by
  sorry

/-- The partner `W_β` as a permutation of `ℤ`. -/
noncomputable def wqpPerm (r : ℕ) (hr : 2 ≤ r) : Equiv.Perm ℤ :=
  Equiv.ofBijective (wqp r) (wqp_bijective hr)

theorem wqpPerm_apply (hr : 2 ≤ r) (n : ℤ) : wqpPerm r hr n = wqp r n := rfl

/-- **(ratified).**  The partner preserves `ℕ⁺`. -/
theorem wqp_pos_iff (hr : 2 ≤ r) (n : ℤ) : 0 < wqp r n ↔ 0 < n := by
  sorry

end Bijection

/-! ## Theorem D and the one-step inequalities -/

section Steps

variable {r : ℕ}

/-- **(ratified, Theorem D).**  If `W(2k)` is odd then `W(W(2k)) = 2rk`.  Paper proof:
`W(2k) = kα − f = 2j − 1`, `f = {kα} ∈ (0, 1)` (`k ≠ 0` since `W(0) = 0` is even), so
`W(2j − 1) = ⌈jβ⌉ − 1 = ⌈(kα − f + 1)β/2⌉ − 1 = ⌈2rk + (1 − f)β/2⌉ − 1 = 2rk`, as
`0 < (1 − f)β/2 < 1`.  Integer route: with `s = sfl r k`, `s ≤ 2k√m < s + 1`, the claim is
`sfl r ((2rk + s + 1)/2) = 2mk + rs + r − 1`, two polynomial inequalities (`nlinarith`). -/
theorem wq_wq_of_odd (hr : 2 ≤ r) (k : ℤ) (h : wq r (2 * k) % 2 = 1) :
    wq r (wq r (2 * k)) = 2 * r * k := by
  sorry

/-- **(ratified, Theorem D for the partner).**  If `W'(2k − 1)` is even then
`W'(W'(2k − 1)) = 2rk − 1`.  Paper proof: `W'(2k − 1) = kα − f = 2j`, so
`W'(2j) = ⌈jβ⌉ − 1 = ⌈2rk − fβ/2⌉ − 1 = 2rk − 1`. -/
theorem wqp_wqp_of_even (hr : 2 ≤ r) (k : ℤ) (h : wqp r (2 * k - 1) % 2 = 0) :
    wqp r (wqp r (2 * k - 1)) = 2 * r * k - 1 := by
  sorry

/-- **(ratified).**  `1` is a fixed point: `⌊β⌋ = 1`. -/
theorem wq_one (hr : 2 ≤ r) : wq r 1 = 1 := by
  sorry

/-- **(ratified).**  Even ascent, with the slope bounds `4r − 2 < α < 4r`:
`(4r − 2)k ≤ W(2k) < 4rk` for `k ≥ 1`.  Paper proof: `(2r − 2)k ≤ ⌊2k√m⌋ < 2rk`. -/
theorem wq_two_mul_bounds (hr : 2 ≤ r) {k : ℤ} (hk : 1 ≤ k) :
    (4 * r - 2) * k ≤ wq r (2 * k) ∧ wq r (2 * k) < 4 * r * k := by
  sorry

/-- **(ratified).**  Odd descent: `j ≤ W(2j − 1)`, and `W(2j − 1) < 2j − 1` for `j ≥ 2`.
Paper proof: `⌊jβ⌋ < 2j − 1 ⟸ j(2 − β) > 1`, true for `j ≥ 2` as `β < 6/5`. -/
theorem wq_two_mul_sub_one_bounds (hr : 2 ≤ r) {j : ℤ} (hj : 1 ≤ j) :
    j ≤ wq r (2 * j - 1) ∧ (2 ≤ j → wq r (2 * j - 1) < 2 * j - 1) := by
  sorry

/-- **(ratified).**  Partner steps: `k ≤ W'(2k) < 2k` and `2k − 1 < W'(2k − 1)` for `k ≥ 1`. -/
theorem wqp_bounds (hr : 2 ≤ r) {k : ℤ} (hk : 1 ≤ k) :
    k ≤ wqp r (2 * k) ∧ wqp r (2 * k) < 2 * k ∧ 2 * k - 1 < wqp r (2 * k - 1) := by
  sorry

end Steps

/-! ## Theorem F: orbit classification of `W_α` -/

section TheoremF

variable {r : ℕ}

/-- Entry points: even `y > 0` with an odd preimage (`y = ⌊jβ⌋`) that is not `2rk` for a `k`
with `W(2k)` odd (the only way the second preimage is even, by Theorem D). -/
def IsEntry (r : ℕ) (y : ℤ) : Prop :=
  0 < y ∧ y % 2 = 0 ∧ (∃ j : ℤ, wq r (2 * j - 1) = y) ∧
    ∀ k : ℤ, wq r (2 * k) % 2 = 1 → 2 * r * k ≠ y

/-- **(ratified).**  The paper's form: `y` is an entry point iff it is even and positive with
`W⁻¹(y)` and `W⁻²(y)` odd.  Paper proof: `W⁻¹ y` is odd iff `y ∈ W(odd)`; if it is odd and
`W⁻² y = 2k` is even, Theorem D gives `y = 2rk`; conversely `y = 2rk` with `W(2k)` odd has
`W⁻¹ y = W(2k)`, `W⁻² y = 2k`. -/
theorem isEntry_iff (hr : 2 ≤ r) (y : ℤ) :
    IsEntry r y ↔ 0 < y ∧ y % 2 = 0 ∧ (wqPerm r hr).symm y % 2 = 1 ∧
      (wqPerm r hr).symm ((wqPerm r hr).symm y) % 2 = 1 := by
  sorry

/-- **(ratified).**  Orbits of positive points stay positive. -/
theorem permOrbit_subset_pos (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    permOrbit (wqPerm r hr) x ⊆ {y | 0 < y} := by
  sorry

/-- **(ratified).**  `{1}` is a finite orbit. -/
theorem permOrbit_wqPerm_one (hr : 2 ≤ r) : permOrbit (wqPerm r hr) 1 = {1} := by
  sorry

/-- **(ratified, Theorem F, structure).**  Every orbit through `x > 1` contains exactly one entry
point.  Paper proof: (a) the even points of a forward orbit strictly increase (`W(2k) > 2k`, or
`W(2k)` odd and `W²(2k) = 2rk > 2k`); (b) after an even point no two odd points are adjacent
(Theorem D); (c) odd points `> 1` strictly decrease (`wq_two_mul_sub_one_bounds`).  An orbit
`≠ {1}` has an even point (else its forward orbit is an infinite decreasing sequence in `ℕ⁺`),
and its even points increase, so there is a first one, `e`; the two points before `e` are odd
(by minimality), so `e` is an entry point.  Any later even point `y` has an even point two steps
back or `W⁻¹ y` even (b), so it is not an entry point. -/
theorem existsUnique_isEntry_mem_orbit (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    ∃! e, IsEntry r e ∧ e ∈ permOrbit (wqPerm r hr) x := by
  sorry

/-- **(ratified, Theorem F, minimum).**  An entry point is strictly below every other point of
its orbit.  Paper proof: before `e` all points are odd and increase backward (c); after `e` the
even points increase (a) and each odd point is `W(2k) > 2k ≥ e`. -/
theorem isEntry_lt_of_mem_orbit (hr : 2 ≤ r) {e y : ℤ} (he : IsEntry r e)
    (hy : y ∈ permOrbit (wqPerm r hr) e) (hne : y ≠ e) : e < y := by
  sorry

/-- **(ratified, Theorem F, no other finite orbit).**  Every orbit through `x > 1` is
infinite. -/
theorem permOrbit_wqPerm_infinite (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    (permOrbit (wqPerm r hr) x).Infinite := by
  sorry

/-- **(ratified, Theorem F, forward escape).**  For `x > 1` the forward orbit tends to `∞`. -/
theorem tendsto_wqPerm_pow (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => (wqPerm r hr ^ n) x) atTop atTop := by
  sorry

/-- **(ratified, Theorem F, backward escape).**  For `x > 1` the backward orbit tends to `∞`. -/
theorem tendsto_wqPerm_pow_neg (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => (wqPerm r hr ^ (-(n : ℤ))) x) atTop atTop := by
  sorry

/-- **(ratified, Theorem F, orbit minima).**  For `x > 0`: `x` is the minimum of its orbit iff
`x = 1` or `x` is an entry point. -/
theorem isOrbitMin_iff (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    (∀ y ∈ permOrbit (wqPerm r hr) x, x ≤ y) ↔ x = 1 ∨ IsEntry r x := by
  sorry

/-- **(ratified, Theorem F, indexing).**  The orbits meeting `ℕ⁺` are indexed by `{1}` and the
entry points. -/
theorem permOrbit_bijOn (hr : 2 ≤ r) :
    Set.BijOn (permOrbit (wqPerm r hr)) ({1} ∪ {y | IsEntry r y})
      {O | ∃ x : ℤ, 0 < x ∧ O = permOrbit (wqPerm r hr) x} := by
  sorry

/-- **(ratified, Theorem F, conclusion).**  `W_α` has infinitely many infinite orbits.  Paper
proof: `C = 2ℤ ∪ W(2ℤ)` is a trap (`W(2k)` even stays in `2ℤ`; `W(2k)` odd maps to `2rk`), its
entry points `C ∖ W(C)` are the even `y` with `W⁻¹ y, W⁻² y` odd (`isEntry_iff`), and they are
infinitely many by `minCount_ge` below (or apply `permOrbit_bijOn` and
`permOrbit_wqPerm_infinite`). -/
theorem wqPerm_infinitelyManyInfiniteOrbits (hr : 2 ≤ r) :
    InfinitelyManyInfiniteOrbits (wqPerm r hr) := by
  sorry

end TheoremF

/-! ## Theorem F: counting orbit minima -/

section Count

variable {r : ℕ}

/-- `A(X) = #{j ≥ 1 : ⌊jβ⌋ ≤ X, ⌊jβ⌋ even}` (`⌊jβ⌋ ≥ j`, so `j ≤ X` suffices). -/
def countA (r X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun j : ℕ =>
    wq r (2 * j - 1) ≤ X ∧ wq r (2 * j - 1) % 2 = 0).card

/-- `B(X) = #{k ≥ 1 : 2rk ≤ X, ⌊kα⌋ odd}`. -/
def countB (r X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun k : ℕ => 2 * r * k ≤ X ∧ wq r (2 * k) % 2 = 1).card

open Classical in
/-- The number of orbits of `W_α` with minimum in `[1, X]`. -/
noncomputable def minCount (r : ℕ) (hr : 2 ≤ r) (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun x => ∀ y ∈ permOrbit (wqPerm r hr) x, x ≤ y).card

/-- **(ratified, Theorem F, exact count).**  `#{orbit minima ≤ X} = 1 + A(X) − B(X)`.  Paper
proof: by `isOrbitMin_iff` the minima in `[1, X]` are `1` and the entry points `≤ X`.  The even
`y ≤ X` in `W(odd)` are the even `⌊jβ⌋ ≤ X` (`A(X)`); among them the `2rk` with `W(2k)` odd
(`B(X)`, an injective image of `k`) are exactly the non-entries. -/
theorem minCount_add_countB (hr : 2 ≤ r) {X : ℕ} (hX : 1 ≤ X) :
    minCount r hr X + countB r X = 1 + countA r X := by
  sorry

/-- **(ratified, Theorem F, unconditional lower bound).**
`#{orbit minima ≤ X} ≥ 1 + ⌊X/2⌋ − ⌊X/(4r − 2)⌋ − ⌊X/2r⌋`, linear in `X` (`≥ X/12`).
Paper proof: `A(X) = #{even y ≤ X} − #{even ⌊kα⌋ ≤ X} ≥ ⌊X/2⌋ − ⌊X/(4r − 2)⌋` by
`wq_two_mul_bounds`, and `B(X) ≤ ⌊X/2r⌋`. -/
theorem minCount_ge (hr : 2 ≤ r) {X : ℕ} (hX : 1 ≤ X) :
    1 + (X : ℤ) / 2 - X / (4 * r - 2) - X / (2 * r) ≤ minCount r hr X := by
  sorry

/-- **(ratified).**  Every minimum other than `1` is even. -/
theorem minCount_le (hr : 2 ≤ r) (X : ℕ) : minCount r hr X ≤ 1 + X / 2 := by
  sorry

/-- **Literature hypothesis (Bohl, Sierpiński, Weyl 1909-1916; not in Mathlib).**
`k√(r² − r)` is equidistributed mod 1, so `⌊2k√(r² − r)⌋` is odd (`{k√(r² − r)} ≥ 1/2`) for a
set of `k` of density `1/2`.  True for every `r ≥ 2` since `√(r² − r)` is irrational. -/
def SflOddDensityHalf (r : ℕ) : Prop :=
  Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter fun k : ℕ => sfl r k % 2 = 1).card : ℝ) / N)
    atTop (𝓝 (1 / 2))

/-- **(ratified, Theorem F, density, conditional on equidistribution).**  The orbit minima have
density `d_r = 1/(2β) − 1/(4r) = (r − 1 + √(r² − r))/(4r)`.  Paper proof: `⌊jβ⌋` is even iff
`sfl r j` is odd, and `⌊kα⌋` is odd iff `sfl r k` is odd; `A(X)` counts `j ≤ J(X) ∼ X/β`,
`B(X)` counts `k ≤ X/2r`; apply the hypothesis along `J(X)` and `⌊X/2r⌋`, and
`1/β = α/(4r)`. -/
theorem tendsto_minCount (hr : 2 ≤ r) (h : SflOddDensityHalf r) :
    Tendsto (fun X : ℕ => (minCount r hr X : ℝ) / X) atTop
      (𝓝 (((r : ℝ) - 1 + √((r : ℝ) ^ 2 - r)) / (4 * r))) := by
  sorry

end Count

/-! ## The partner `W_β`: no finite orbit in `ℕ⁺` -/

section Partner

variable {r : ℕ}

/-- Partner entry points: odd `y > 0` with an even preimage (`y = ⌊kβ⌋`) that is not `2rj − 1`
for a `j` with `W'(2j − 1)` even. -/
def IsEntryP (r : ℕ) (y : ℤ) : Prop :=
  0 < y ∧ y % 2 = 1 ∧ (∃ k : ℤ, wqp r (2 * k) = y) ∧
    ∀ j : ℤ, wqp r (2 * j - 1) % 2 = 0 → 2 * r * j - 1 ≠ y

/-- **(ratified).**  Partner entry points are the positive odd `y` with `W'⁻¹ y`, `W'⁻² y`
even. -/
theorem isEntryP_iff (hr : 2 ≤ r) (y : ℤ) :
    IsEntryP r y ↔ 0 < y ∧ y % 2 = 1 ∧ (wqpPerm r hr).symm y % 2 = 0 ∧
      (wqpPerm r hr).symm ((wqpPerm r hr).symm y) % 2 = 0 := by
  sorry

/-- **(ratified, partner structure).**  Every orbit through `x > 0` contains exactly one partner
entry point.  Paper proof: Theorem F with parities swapped: odd points of a forward orbit
increase (`W'(2k − 1) > 2k − 1`, or `W'²(2k − 1) = 2rk − 1 > 2k − 1`), even points decrease
(`W'(2k) < 2k`), so an all-even orbit is impossible and there is a first odd point. -/
theorem existsUnique_isEntryP_mem_orbit (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    ∃! e, IsEntryP r e ∧ e ∈ permOrbit (wqpPerm r hr) x := by
  sorry

/-- **(ratified, partner minimum).** -/
theorem isEntryP_lt_of_mem_orbit (hr : 2 ≤ r) {e y : ℤ} (he : IsEntryP r e)
    (hy : y ∈ permOrbit (wqpPerm r hr) e) (hne : y ≠ e) : e < y := by
  sorry

/-- **(ratified, partner: no finite orbit in `ℕ⁺`).** -/
theorem permOrbit_wqpPerm_infinite (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    (permOrbit (wqpPerm r hr) x).Infinite := by
  sorry

/-- **(ratified, partner forward escape).** -/
theorem tendsto_wqpPerm_pow (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (wqpPerm r hr ^ n) x) atTop atTop := by
  sorry

/-- **(ratified, partner backward escape).** -/
theorem tendsto_wqpPerm_pow_neg (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (wqpPerm r hr ^ (-(n : ℤ))) x) atTop atTop := by
  sorry

/-- **(ratified, partner orbit minima).**  For `x > 0`: `x` is the minimum of its orbit iff `x`
is a partner entry point. -/
theorem isOrbitMinP_iff (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    (∀ y ∈ permOrbit (wqpPerm r hr) x, x ≤ y) ↔ IsEntryP r x := by
  sorry

/-- **(ratified, partner conclusion).** -/
theorem wqpPerm_infinitelyManyInfiniteOrbits (hr : 2 ≤ r) :
    InfinitelyManyInfiniteOrbits (wqpPerm r hr) := by
  sorry

/-- `A′(X) = #{k ≥ 1 : ⌊kβ⌋ ≤ X odd}`. -/
def countAP (r X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun k : ℕ => wqp r (2 * k) ≤ X ∧ wqp r (2 * k) % 2 = 1).card

/-- `B′(X) = #{j ≥ 1 : 2rj − 1 ≤ X, ⌊jα⌋ even}`. -/
def countBP (r X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun j : ℕ =>
    2 * r * j - 1 ≤ (X : ℤ) ∧ wqp r (2 * j - 1) % 2 = 0).card

open Classical in
/-- The number of orbits of `W_β` with minimum in `[1, X]`. -/
noncomputable def minCountP (r : ℕ) (hr : 2 ≤ r) (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun x => ∀ y ∈ permOrbit (wqpPerm r hr) x, x ≤ y).card

/-- **(ratified, partner exact count).**  `#{orbit minima ≤ X} = A′(X) − B′(X)`. -/
theorem minCountP_add_countBP (hr : 2 ≤ r) (X : ℕ) :
    minCountP r hr X + countBP r X = countAP r X := by
  sorry

/-- **(ratified, partner density, conditional on equidistribution).**  Same `d_r`:
`⌊kβ⌋ = 2rk − sfl − 1` is odd iff `sfl r k` is even. -/
theorem tendsto_minCountP (hr : 2 ≤ r) (h : SflOddDensityHalf r) :
    Tendsto (fun X : ℕ => (minCountP r hr X : ℝ) / X) atTop
      (𝓝 (((r : ℝ) - 1 + √((r : ℝ) ^ 2 - r)) / (4 * r))) := by
  sorry

end Partner

end CollatzMoonshot.WythoffQuadratic
