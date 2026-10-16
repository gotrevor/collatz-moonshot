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
  unfold wq
  rw [if_pos (by omega), show 2 * k / 2 = k by omega]
  ring

/-- **(ratified).**  Odd branch. -/
theorem wq_two_mul_sub_one (r : ℕ) (k : ℤ) : wq r (2 * k - 1) = 2 * r * k - sfl r k - 1 := by
  unfold wq
  rw [if_neg (by omega), show (2 * k - 1 + 1) / 2 = k by omega]
  ring

/-- **(ratified).**  Partner, even branch. -/
theorem wqp_two_mul (r : ℕ) (k : ℤ) : wqp r (2 * k) = 2 * r * k - sfl r k - 1 := by
  unfold wqp
  rw [if_pos (by omega), show 2 * k / 2 = k by omega]
  ring

/-- **(ratified).**  Partner, odd branch. -/
theorem wqp_two_mul_sub_one (r : ℕ) (k : ℤ) : wqp r (2 * k - 1) = 2 * r * k + sfl r k := by
  unfold wqp
  rw [if_neg (by omega), show (2 * k - 1 + 1) / 2 = k by omega]
  ring

/-- **(ratified).**  The partner is `wq` precomposed with the involution `2k ↔ 2k − 1`. -/
theorem wqp_eq_wq (r : ℕ) (n : ℤ) : wqp r n = wq r (if n % 2 = 0 then n - 1 else n + 1) := by
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k - 1 := ⟨(n + 1) / 2, by omega⟩
  · rw [if_pos (by omega), wqp_two_mul, wq_two_mul_sub_one]
  · rw [if_neg (by omega), show 2 * k - 1 + 1 = 2 * k by ring, wqp_two_mul_sub_one, wq_two_mul]

/-- The radicand `r² − r` is nonnegative for every natural `r`. -/
lemma radicand_nonneg (r : ℕ) : (0 : ℝ) ≤ (r : ℝ) ^ 2 - r := by
  rcases Nat.eq_zero_or_pos r with rfl | h
  · simp
  · have : (1 : ℝ) ≤ r := by exact_mod_cast h
    nlinarith

/-- `(√(r² − r))² = r² − r`. -/
lemma sqrt_sq_radicand (r : ℕ) : √((r : ℝ) ^ 2 - r) ^ 2 = (r : ℝ) ^ 2 - r :=
  Real.sq_sqrt (radicand_nonneg r)

/-- `r − 3/5 < √(r² − r)` for `r ≥ 2`. -/
lemma sqrt_radicand_gt (hr : 2 ≤ r) : (r : ℝ) - 3 / 5 < √((r : ℝ) ^ 2 - r) := by
  have : (2 : ℝ) ≤ r := by exact_mod_cast hr
  rw [Real.lt_sqrt (by linarith)]
  nlinarith

/-- `√(r² − r) < r − 1/2`. -/
lemma sqrt_radicand_lt (hr : 2 ≤ r) : √((r : ℝ) ^ 2 - r) < r - 1 / 2 := by
  have : (2 : ℝ) ≤ r := by exact_mod_cast hr
  rw [Real.sqrt_lt' (by linarith)]
  nlinarith

/-- **(ratified).**  `√(r² − r)` is irrational for `r ≥ 2`: `(r − 1)² < r² − r < r²`. -/
theorem irrational_sqrt (hr : 2 ≤ r) : Irrational √((r : ℝ) ^ 2 - r) := by
  have hrr : r ≤ r ^ 2 := by nlinarith
  have hc : ((r : ℝ) ^ 2 - r) = ((r ^ 2 - r : ℕ) : ℝ) := by
    rw [Nat.cast_sub hrr]; push_cast; ring
  rw [hc, irrational_sqrt_natCast_iff]
  rintro ⟨t, ht⟩
  have h1 : t * t + r = r * r := by rw [sq] at ht hrr; omega
  rcases lt_or_ge t r with h | h
  · have : t + 1 ≤ r := h
    nlinarith
  · nlinarith

/-- **(ratified).**  `α + β = 4r`. -/
theorem alphaQ_add_betaQ (r : ℕ) : alphaQ r + betaQ r = 4 * r := by
  unfold alphaQ betaQ; ring

/-- **(ratified).**  `αβ = 4r`. -/
theorem alphaQ_mul_betaQ (r : ℕ) : alphaQ r * betaQ r = 4 * r := by
  unfold alphaQ betaQ
  linear_combination (-4 : ℝ) * sqrt_sq_radicand r

/-- **(ratified).**  `1 < β < 6/5` for `r ≥ 2`.  Paper proof: `β = 2r/(r + √(r² − r))`;
`β > 1 ⇔ √(r² − r) < r`, and `β < 6/5 ⇔ √(r² − r) > 2r/3 ⇔ 5r² > 9r`.  (At `r = 2`,
`β = 4 − 2√2 ≈ 1.1716`.) -/
theorem one_lt_betaQ_lt (hr : 2 ≤ r) : 1 < betaQ r ∧ betaQ r < 6 / 5 := by
  unfold betaQ
  constructor <;> linarith [sqrt_radicand_lt hr, sqrt_radicand_gt hr]

/-- **(ratified).**  `α` and `β` are Hölder conjugate: `1/α + 1/β = (α + β)/(αβ) = 1`. -/
theorem alphaQ_holderConjugate (hr : 2 ≤ r) : (alphaQ r).HolderConjugate (betaQ r) := by
  have hb := one_lt_betaQ_lt hr
  have hq := Real.sqrt_nonneg ((r : ℝ) ^ 2 - r)
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have ha : 0 < alphaQ r := by unfold alphaQ; linarith
  refine ⟨?_, ha, by linarith⟩
  rw [inv_one, inv_add_inv ha.ne' (by linarith), alphaQ_add_betaQ, alphaQ_mul_betaQ,
    div_self (by positivity)]

/-- `sqrtPart r k` is `Nat.sqrt` of `(2|k|√m)²`. -/
lemma sqrtPart_spec (r : ℕ) (k : ℤ) :
    (sqrtPart r k : ℝ) ≤ 2 * |(k : ℝ)| * √((r : ℝ) ^ 2 - r) ∧
      2 * |(k : ℝ)| * √((r : ℝ) ^ 2 - r) < sqrtPart r k + 1 := by
  have hrr : r ≤ r ^ 2 := by nlinarith
  have hn : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hsq : √((4 * k.natAbs ^ 2 * (r ^ 2 - r) : ℕ) : ℝ) =
      2 * |(k : ℝ)| * √((r : ℝ) ^ 2 - r) := by
    rw [show ((4 * k.natAbs ^ 2 * (r ^ 2 - r) : ℕ) : ℝ) =
        (2 * |(k : ℝ)|) ^ 2 * ((r : ℝ) ^ 2 - r) by
      rw [Nat.cast_mul, Nat.cast_sub hrr, Nat.cast_mul, Nat.cast_pow, hn]; push_cast; ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  unfold sqrtPart
  rw [← hsq]
  exact ⟨Real.nat_sqrt_le_real_sqrt, Real.real_sqrt_lt_nat_sqrt_succ⟩

/-- `2k√m` is irrational for `k ≠ 0`. -/
lemma irrational_two_mul_sqrt (hr : 2 ≤ r) {k : ℤ} (hk : k ≠ 0) :
    Irrational (2 * k * √((r : ℝ) ^ 2 - r)) := by
  have := (irrational_sqrt hr).intCast_mul (m := 2 * k) (by omega)
  simpa using this

/-- `sfl r k ≤ 2k√m < sfl r k + 1`. -/
lemma sfl_bounds (hr : 2 ≤ r) (k : ℤ) :
    (sfl r k : ℝ) ≤ 2 * k * √((r : ℝ) ^ 2 - r) ∧
      2 * k * √((r : ℝ) ^ 2 - r) < sfl r k + 1 := by
  obtain ⟨h1, h2⟩ := sqrtPart_spec r k
  unfold sfl
  split_ifs with hk
  · rw [abs_of_nonneg (by exact_mod_cast hk : (0 : ℝ) ≤ k)] at h1 h2
    exact ⟨h1, h2⟩
  · have hk' : (k : ℝ) < 0 := by exact_mod_cast (not_le.mp hk)
    rw [abs_of_neg hk'] at h1 h2
    have hne := (irrational_two_mul_sqrt hr (show k ≠ 0 by omega)).neg.ne_nat (sqrtPart r k)
    have h3 : (sqrtPart r k : ℝ) < 2 * -(k : ℝ) * √((r : ℝ) ^ 2 - r) := by
      refine lt_of_le_of_ne h1 fun h => hne ?_
      rw [h]; ring
    push_cast
    constructor <;> linarith

/-- **(ratified).**  `sfl` is the real floor.  Paper proof: `k ≥ 0` is `Nat.sqrt`'s spec
(`Real.nat_sqrt_le_real_sqrt`, `Real.real_sqrt_lt_nat_sqrt_succ`); for `k < 0`, the value
`2|k|√(r² − r)` is irrational, so `⌊−y⌋ = −⌊y⌋ − 1`. -/
theorem sfl_eq_floor (hr : 2 ≤ r) (k : ℤ) :
    sfl r k = ⌊(2 * k : ℝ) * √((r : ℝ) ^ 2 - r)⌋ := by
  rw [eq_comm, Int.floor_eq_iff]
  exact sfl_bounds hr k

/-- Strictness: `sfl r k < 2k√m` for `k ≠ 0`. -/
lemma sfl_lt (hr : 2 ≤ r) {k : ℤ} (hk : k ≠ 0) :
    (sfl r k : ℝ) < 2 * k * √((r : ℝ) ^ 2 - r) :=
  lt_of_le_of_ne (sfl_bounds hr k).1 ((irrational_two_mul_sqrt hr hk).ne_int _).symm

/-- Pinning `sfl` by its real bounds. -/
lemma sfl_eq_of (hr : 2 ≤ r) {j T : ℤ} (h1 : (T : ℝ) ≤ 2 * j * √((r : ℝ) ^ 2 - r))
    (h2 : 2 * j * √((r : ℝ) ^ 2 - r) < T + 1) : sfl r j = T := by
  rw [sfl_eq_floor hr, Int.floor_eq_iff]
  exact ⟨h1, h2⟩

lemma sfl_zero (r : ℕ) : sfl r 0 = 0 := by
  simp [sfl, sqrtPart]

/-- For `k ≥ 1`: `(2r − 2)k ≤ sfl r k ≤ (2r − 1)k − 1`. -/
lemma sfl_pos_bounds (hr : 2 ≤ r) {k : ℤ} (hk : 1 ≤ k) :
    (2 * r - 2) * k ≤ sfl r k ∧ sfl r k + 1 ≤ (2 * r - 1) * k := by
  obtain ⟨h1, h2⟩ := sfl_bounds hr k
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have g1 := mul_lt_mul_of_pos_left (sqrt_radicand_gt hr) (show (0 : ℝ) < k by linarith)
  have g2 := mul_lt_mul_of_pos_left (sqrt_radicand_lt hr) (show (0 : ℝ) < k by linarith)
  have a : (((2 * r - 2) * k - 1 : ℤ) : ℝ) < sfl r k := by push_cast; nlinarith
  have b : (sfl r k : ℝ) < (((2 * r - 1) * k : ℤ) : ℝ) := by push_cast; nlinarith
  have a' := Int.cast_lt.mp a
  have b' := Int.cast_lt.mp b
  omega

/-- For `k ≥ 2`: `(2r − 2)k + 1 ≤ sfl r k`. -/
lemma sfl_ge_of_two_le (hr : 2 ≤ r) {k : ℤ} (hk : 2 ≤ k) :
    (2 * r - 2) * k + 1 ≤ sfl r k := by
  obtain ⟨h1, h2⟩ := sfl_bounds hr k
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have g1 := mul_lt_mul_of_pos_left (sqrt_radicand_gt hr) (show (0 : ℝ) < k by linarith)
  have a : (((2 * r - 2) * k : ℤ) : ℝ) < sfl r k := by push_cast; nlinarith
  have a' := Int.cast_lt.mp a
  omega

/-- For `k ≤ 0`: `2rk ≤ sfl r k ≤ 0`. -/
lemma sfl_nonpos_bounds (hr : 2 ≤ r) {k : ℤ} (hk : k ≤ 0) :
    2 * r * k ≤ sfl r k ∧ sfl r k ≤ 0 := by
  obtain ⟨h1, h2⟩ := sfl_bounds hr k
  have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
  have hq := Real.sqrt_nonneg ((r : ℝ) ^ 2 - r)
  have g2 := mul_le_mul_of_nonpos_left (sqrt_radicand_lt hr).le hk'
  have a : (((2 * r * k) - 1 : ℤ) : ℝ) < sfl r k := by push_cast; nlinarith
  have b : (sfl r k : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; nlinarith
  have a' := Int.cast_lt.mp a
  have b' := Int.cast_lt.mp b
  omega

/-- The increments of `sfl` are `2r − 2` or `2r − 1`. -/
lemma sfl_succ_bounds (hr : 2 ≤ r) (k : ℤ) :
    2 * r - 2 ≤ sfl r (k + 1) - sfl r k ∧ sfl r (k + 1) - sfl r k ≤ 2 * r - 1 := by
  obtain ⟨h1, h2⟩ := sfl_bounds hr k
  obtain ⟨h3, h4⟩ := sfl_bounds hr (k + 1)
  push_cast at h3 h4
  have g1 := sqrt_radicand_gt hr
  have g2 := sqrt_radicand_lt hr
  have a : ((2 * r - 3 : ℤ) : ℝ) < ((sfl r (k + 1) - sfl r k : ℤ) : ℝ) := by
    push_cast; linarith
  have b : ((sfl r (k + 1) - sfl r k : ℤ) : ℝ) < ((2 * r : ℤ) : ℝ) := by
    push_cast; linarith
  have a' := Int.cast_lt.mp a
  have b' := Int.cast_lt.mp b
  omega

/-- **(ratified).**  `W(2k) = ⌊kα⌋` for every `k ∈ ℤ`. -/
theorem wq_two_mul_eq_floor (hr : 2 ≤ r) (k : ℤ) : wq r (2 * k) = ⌊(k : ℝ) * alphaQ r⌋ := by
  rw [wq_two_mul, sfl_eq_floor hr]
  unfold alphaQ
  rw [show (k : ℝ) * (2 * r + 2 * √((r : ℝ) ^ 2 - r)) =
      2 * k * √((r : ℝ) ^ 2 - r) + ((2 * r * k : ℤ) : ℝ) by push_cast; ring,
    Int.floor_add_intCast]
  ring

/-- **(ratified).**  `W(2k − 1) = ⌈kβ⌉ − 1` for every `k ∈ ℤ` (Mathlib's `beattySeq'`). -/
theorem wq_two_mul_sub_one_eq_ceil (hr : 2 ≤ r) (k : ℤ) :
    wq r (2 * k - 1) = ⌈(k : ℝ) * betaQ r⌉ - 1 := by
  rw [wq_two_mul_sub_one, sfl_eq_floor hr]
  unfold betaQ
  rw [show (k : ℝ) * (2 * r - 2 * √((r : ℝ) ^ 2 - r)) =
      -(2 * k * √((r : ℝ) ^ 2 - r)) + ((2 * r * k : ℤ) : ℝ) by push_cast; ring,
    Int.ceil_add_intCast, Int.ceil_neg]
  ring

/-- **(ratified).**  `W(2k − 1) = ⌊kβ⌋` for `k ≠ 0` (`kβ` is irrational). -/
theorem wq_two_mul_sub_one_eq_floor (hr : 2 ≤ r) {k : ℤ} (hk : k ≠ 0) :
    wq r (2 * k - 1) = ⌊(k : ℝ) * betaQ r⌋ := by
  rw [wq_two_mul_sub_one]
  unfold betaQ
  rw [show (k : ℝ) * (2 * r - 2 * √((r : ℝ) ^ 2 - r)) =
      -(2 * k * √((r : ℝ) ^ 2 - r)) + ((2 * r * k : ℤ) : ℝ) by push_cast; ring,
    Int.floor_add_intCast, Int.floor_neg]
  have h : ⌈2 * (k : ℝ) * √((r : ℝ) ^ 2 - r)⌉ = sfl r k + 1 := by
    rw [Int.ceil_eq_iff]
    push_cast
    constructor <;> linarith [sfl_lt hr hk, (sfl_bounds hr k).2]
  rw [h]
  ring

/-- **(ratified).**  Partner: `W'(2k) = ⌊kβ⌋` for `k ≠ 0`. -/
theorem wqp_two_mul_eq_floor (hr : 2 ≤ r) {k : ℤ} (hk : k ≠ 0) :
    wqp r (2 * k) = ⌊(k : ℝ) * betaQ r⌋ := by
  rw [wqp_two_mul, ← wq_two_mul_sub_one, wq_two_mul_sub_one_eq_floor hr hk]

/-- **(ratified).**  Partner: `W'(2k − 1) = ⌊kα⌋`. -/
theorem wqp_two_mul_sub_one_eq_floor (hr : 2 ≤ r) (k : ℤ) :
    wqp r (2 * k - 1) = ⌊(k : ℝ) * alphaQ r⌋ := by
  rw [wqp_two_mul_sub_one, ← wq_two_mul, wq_two_mul_eq_floor hr]

end Bridge

/-! ## Bijectivity -/

section Bijection

variable {r : ℕ}

/-- The even branch is strictly increasing. -/
lemma wq_even_strictMono (hr : 2 ≤ r) : StrictMono fun k => wq r (2 * k) := by
  refine strictMono_int_of_lt_succ fun k => ?_
  simp only [wq_two_mul]
  have := sfl_succ_bounds hr k
  nlinarith

/-- The odd branch is strictly increasing. -/
lemma wq_odd_strictMono (hr : 2 ≤ r) : StrictMono fun k => wq r (2 * k - 1) := by
  refine strictMono_int_of_lt_succ fun k => ?_
  simp only [wq_two_mul_sub_one]
  have := sfl_succ_bounds hr k
  nlinarith

/-- **(ratified).**  `W` is a bijection of `ℤ`.  Paper proof: the even branch is
`k ↦ beattySeq α k`, the odd branch `k ↦ beattySeq' β k` (`wq_two_mul_eq_floor`,
`wq_two_mul_sub_one_eq_ceil`), both strictly increasing (`α, β > 1`), with complementary ranges
(`compl_beattySeq` with `alphaQ_holderConjugate`). -/
theorem wq_bijective (hr : 2 ≤ r) : Function.Bijective (wq r) := by
  have hc := compl_beattySeq (alphaQ_holderConjugate hr)
  have cross : ∀ a b : ℤ, wq r (2 * a) ≠ wq r (2 * b - 1) := by
    intro a b h
    have hmem : beattySeq' (betaQ r) b ∈ {x | ∃ k, beattySeq' (betaQ r) k = x} := ⟨b, rfl⟩
    rw [← hc] at hmem
    refine hmem ⟨a, ?_⟩
    simp only [beattySeq, beattySeq']
    rw [← wq_two_mul_eq_floor hr, ← wq_two_mul_sub_one_eq_ceil hr, h]
  refine ⟨fun a b h => ?_, fun n => ?_⟩
  · obtain ⟨k, rfl | rfl⟩ : ∃ k, a = 2 * k ∨ a = 2 * k - 1 := ⟨(a + 1) / 2, by omega⟩ <;>
    obtain ⟨l, rfl | rfl⟩ : ∃ l, b = 2 * l ∨ b = 2 * l - 1 := ⟨(b + 1) / 2, by omega⟩
    · rw [(wq_even_strictMono hr).injective h]
    · exact absurd h (cross _ _)
    · exact absurd h.symm (cross _ _)
    · rw [(wq_odd_strictMono hr).injective h]
  · by_cases h : n ∈ {x | ∃ k, beattySeq (alphaQ r) k = x}
    · obtain ⟨k, hk⟩ := h
      exact ⟨2 * k, by rw [wq_two_mul_eq_floor hr]; exact hk⟩
    · rw [← Set.mem_compl_iff, hc] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨2 * k - 1, by rw [wq_two_mul_sub_one_eq_ceil hr]; exact hk⟩

/-- `W_α` as a permutation of `ℤ`. -/
noncomputable def wqPerm (r : ℕ) (hr : 2 ≤ r) : Equiv.Perm ℤ :=
  Equiv.ofBijective (wq r) (wq_bijective hr)

theorem wqPerm_apply (hr : 2 ≤ r) (n : ℤ) : wqPerm r hr n = wq r n := rfl

/-- **(ratified).**  `W` preserves `ℕ⁺` (and hence `ℤ≤0`).  Paper proof: for `k ≥ 1`,
`⌊kα⌋ ≥ 1` and `⌊kβ⌋ ≥ 1`; for `k ≤ 0`, `⌊kα⌋ ≤ 0` and `⌈kβ⌉ − 1 ≤ −1`. -/
theorem wq_pos_iff (hr : 2 ≤ r) (n : ℤ) : 0 < wq r n ↔ 0 < n := by
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k - 1 := ⟨(n + 1) / 2, by omega⟩
  · rw [wq_two_mul]
    rcases le_or_gt k 0 with hk | hk
    · have := sfl_nonpos_bounds hr hk
      constructor
      · intro h; nlinarith
      · intro h; omega
    · have := sfl_pos_bounds hr hk
      constructor
      · intro; omega
      · intro; nlinarith
  · rw [wq_two_mul_sub_one]
    rcases le_or_gt k 0 with hk | hk
    · have := sfl_nonpos_bounds hr hk
      constructor
      · intro h; omega
      · intro h; omega
    · have := sfl_pos_bounds hr hk
      constructor
      · intro; omega
      · intro; nlinarith

/-- **(ratified).**  The partner is a bijection of `ℤ` (`wqp_eq_wq`). -/
theorem wqp_bijective (hr : 2 ≤ r) : Function.Bijective (wqp r) := by
  have hinv : Function.Involutive fun n : ℤ => if n % 2 = 0 then n - 1 else n + 1 := by
    intro n; dsimp only; split_ifs <;> omega
  have : wqp r = wq r ∘ fun n : ℤ => if n % 2 = 0 then n - 1 else n + 1 :=
    funext (wqp_eq_wq r)
  rw [this]
  exact (wq_bijective hr).comp hinv.bijective

/-- The partner `W_β` as a permutation of `ℤ`. -/
noncomputable def wqpPerm (r : ℕ) (hr : 2 ≤ r) : Equiv.Perm ℤ :=
  Equiv.ofBijective (wqp r) (wqp_bijective hr)

theorem wqpPerm_apply (hr : 2 ≤ r) (n : ℤ) : wqpPerm r hr n = wqp r n := rfl

/-- **(ratified).**  The partner preserves `ℕ⁺`. -/
theorem wqp_pos_iff (hr : 2 ≤ r) (n : ℤ) : 0 < wqp r n ↔ 0 < n := by
  rw [wqp_eq_wq, wq_pos_iff hr]
  split_ifs <;> omega

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
  rw [wq_two_mul] at h ⊢
  have hk : k ≠ 0 := by rintro rfl; simp [sfl_zero] at h
  set s := sfl r k with hs
  set q := √((r : ℝ) ^ 2 - r) with hq
  obtain ⟨j, hj⟩ : ∃ j, 2 * r * k + s = 2 * j - 1 := ⟨r * k + (s + 1) / 2, by
    rw [show (2 : ℤ) * r * k = 2 * (r * k) by ring] at h ⊢; omega⟩
  rw [hj, wq_two_mul_sub_one]
  have hT : sfl r j = 2 * ((r : ℤ) ^ 2 - r) * k + r * s + r - 1 := by
    have hjR : (2 * j : ℝ) = 2 * r * k + s + 1 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hj; push_cast at this; linarith
    have e : 2 * (j : ℝ) * q - (((2 * ((r : ℤ) ^ 2 - r) * k + r * s + r - 1 : ℤ)) : ℝ) =
        (r - q) * (2 * k * q - s - 1) + 1 := by
      rw [hjR]; push_cast; linear_combination (2 * (k : ℝ)) * sqrt_sq_radicand r
    have hb := sfl_bounds hr k
    have hl := sfl_lt hr hk
    rw [← hs, ← hq] at hb hl
    have u1 := sqrt_radicand_gt hr
    have u2 := sqrt_radicand_lt hr
    rw [← hq] at u1 u2
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have v1 : 0 < (r - q) * (s + 1 - 2 * k * q) := mul_pos (by linarith) (by linarith)
    have v2 : 0 < (1 - (r - q)) * (s + 1 - 2 * k * q) := mul_pos (by linarith) (by linarith)
    apply sfl_eq_of hr
    · nlinarith
    · nlinarith
  rw [hT]
  linear_combination (r : ℤ) * hj.symm

/-- **(ratified, Theorem D for the partner).**  If `W'(2k − 1)` is even then
`W'(W'(2k − 1)) = 2rk − 1`.  Paper proof: `W'(2k − 1) = kα − f = 2j`, so
`W'(2j) = ⌈jβ⌉ − 1 = ⌈2rk − fβ/2⌉ − 1 = 2rk − 1`. -/
theorem wqp_wqp_of_even (hr : 2 ≤ r) (k : ℤ) (h : wqp r (2 * k - 1) % 2 = 0) :
    wqp r (wqp r (2 * k - 1)) = 2 * r * k - 1 := by
  rw [wqp_two_mul_sub_one] at h ⊢
  set s := sfl r k with hs
  set q := √((r : ℝ) ^ 2 - r) with hq
  obtain ⟨j, hj⟩ : ∃ j, 2 * r * k + s = 2 * j := ⟨r * k + s / 2, by
    rw [show (2 : ℤ) * r * k = 2 * (r * k) by ring] at h ⊢; omega⟩
  rw [hj, wqp_two_mul]
  have hT : sfl r j = 2 * ((r : ℤ) ^ 2 - r) * k + r * s := by
    have hjR : (2 * j : ℝ) = 2 * r * k + s := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hj; push_cast at this; linarith
    have e : 2 * (j : ℝ) * q - (((2 * ((r : ℤ) ^ 2 - r) * k + r * s : ℤ)) : ℝ) =
        (r - q) * (2 * k * q - s) := by
      rw [hjR]; push_cast; linear_combination (2 * (k : ℝ)) * sqrt_sq_radicand r
    have hb := sfl_bounds hr k
    rw [← hs, ← hq] at hb
    have u1 := sqrt_radicand_gt hr
    have u2 := sqrt_radicand_lt hr
    rw [← hq] at u1 u2
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have v1 : 0 ≤ (r - q) * (2 * k * q - s) := mul_nonneg (by linarith) (by linarith)
    have v2 : 0 ≤ (1 - (r - q)) * (2 * k * q - s) := mul_nonneg (by linarith) (by linarith)
    apply sfl_eq_of hr
    · nlinarith
    · nlinarith
  rw [hT]
  linear_combination (r : ℤ) * hj.symm

/-- **(ratified).**  `1` is a fixed point: `⌊β⌋ = 1`. -/
theorem wq_one (hr : 2 ≤ r) : wq r 1 = 1 := by
  have h := wq_two_mul_sub_one r 1
  norm_num at h
  have h1 : sfl r 1 = 2 * r - 2 := by
    apply sfl_eq_of hr
    · push_cast; linarith [sqrt_radicand_gt hr]
    · push_cast; linarith [sqrt_radicand_lt hr]
  rw [h, h1]
  ring

/-- **(ratified).**  Even ascent, with the slope bounds `4r − 2 < α < 4r`:
`(4r − 2)k ≤ W(2k) < 4rk` for `k ≥ 1`.  Paper proof: `(2r − 2)k ≤ ⌊2k√m⌋ < 2rk`. -/
theorem wq_two_mul_bounds (hr : 2 ≤ r) {k : ℤ} (hk : 1 ≤ k) :
    (4 * r - 2) * k ≤ wq r (2 * k) ∧ wq r (2 * k) < 4 * r * k := by
  rw [wq_two_mul]
  have := sfl_pos_bounds hr hk
  constructor <;> nlinarith

/-- **(ratified).**  Odd descent: `j ≤ W(2j − 1)`, and `W(2j − 1) < 2j − 1` for `j ≥ 2`.
Paper proof: `⌊jβ⌋ < 2j − 1 ⟸ j(2 − β) > 1`, true for `j ≥ 2` as `β < 6/5`. -/
theorem wq_two_mul_sub_one_bounds (hr : 2 ≤ r) {j : ℤ} (hj : 1 ≤ j) :
    j ≤ wq r (2 * j - 1) ∧ (2 ≤ j → wq r (2 * j - 1) < 2 * j - 1) := by
  rw [wq_two_mul_sub_one]
  have := sfl_pos_bounds hr hj
  refine ⟨by nlinarith, fun hj2 => ?_⟩
  have := sfl_ge_of_two_le hr hj2
  nlinarith

/-- **(ratified).**  Partner steps: `k ≤ W'(2k) < 2k` and `2k − 1 < W'(2k − 1)` for `k ≥ 1`. -/
theorem wqp_bounds (hr : 2 ≤ r) {k : ℤ} (hk : 1 ≤ k) :
    k ≤ wqp r (2 * k) ∧ wqp r (2 * k) < 2 * k ∧ 2 * k - 1 < wqp r (2 * k - 1) := by
  rw [wqp_two_mul, wqp_two_mul_sub_one]
  have := sfl_pos_bounds hr hk
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

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
