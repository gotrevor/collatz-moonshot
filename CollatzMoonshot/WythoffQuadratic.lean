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

/-! ### An abstract skeleton for both classifications

`σ` preserves `ℕ⁺`; points of the class `E` climb (`up`), an `E`-point whose image leaves `E`
comes back to `E` higher two steps later (`twoStep`), and points outside `E` do not climb
(`down`).  For `W` the class is the evens, for `W'` the odds. -/

section Skeleton

/-- The skeleton hypotheses. -/
structure Skel (σ : Equiv.Perm ℤ) (E : ℤ → Prop) : Prop where
  pos : ∀ y, 0 < σ y ↔ 0 < y
  up : ∀ y, 0 < y → E y → y < σ y
  twoStep : ∀ y, 0 < y → E y → ¬E (σ y) → E (σ (σ y)) ∧ y < σ (σ y)
  down : ∀ y, 0 < y → ¬E y → σ y ≤ y

/-- Abstract entry points: a positive `E`-point whose two predecessors are outside `E`. -/
def SkEntry (σ : Equiv.Perm ℤ) (E : ℤ → Prop) (y : ℤ) : Prop :=
  0 < y ∧ E y ∧ ¬E (σ.symm y) ∧ ¬E (σ.symm (σ.symm y))

variable {σ : Equiv.Perm ℤ} {E : ℤ → Prop}

lemma mem_permOrbit_iff {x y : ℤ} : y ∈ permOrbit σ x ↔ ∃ t : ℤ, (σ ^ t) x = y :=
  Set.mem_range

lemma mem_permOrbit_self (x : ℤ) : x ∈ permOrbit σ x := ⟨0, by simp⟩

lemma zpow_mem_permOrbit (x : ℤ) (t : ℤ) : (σ ^ t) x ∈ permOrbit σ x := ⟨t, rfl⟩

lemma apply_mem_permOrbit {x y : ℤ} (h : y ∈ permOrbit σ x) : σ y ∈ permOrbit σ x := by
  obtain ⟨t, rfl⟩ := mem_permOrbit_iff.1 h
  exact ⟨1 + t, by dsimp only; rw [zpow_add, zpow_one, Equiv.Perm.mul_apply]⟩

lemma symm_mem_permOrbit {x y : ℤ} (h : y ∈ permOrbit σ x) : σ.symm y ∈ permOrbit σ x := by
  obtain ⟨t, rfl⟩ := mem_permOrbit_iff.1 h
  exact ⟨-1 + t, by
    dsimp only; rw [zpow_add, zpow_neg_one, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv]⟩

lemma permOrbit_eq_of_mem {x y : ℤ} (h : y ∈ permOrbit σ x) : permOrbit σ y = permOrbit σ x := by
  obtain ⟨t, rfl⟩ := mem_permOrbit_iff.1 h
  ext z
  simp only [mem_permOrbit_iff]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s + t, by rw [zpow_add, Equiv.Perm.mul_apply]⟩
  · rintro ⟨s, rfl⟩
    refine ⟨s - t, ?_⟩
    rw [← Equiv.Perm.mul_apply, ← zpow_add, sub_add_cancel]

/-- A property closed under `σ` and `σ⁻¹` holds on the whole orbit. -/
lemma permOrbit_induction (P : ℤ → Prop) {x : ℤ} (h0 : P x) (h1 : ∀ y, P y → P (σ y))
    (h2 : ∀ y, P y → P (σ.symm y)) : ∀ y ∈ permOrbit σ x, P y := by
  intro y hy
  obtain ⟨t, rfl⟩ := mem_permOrbit_iff.1 hy
  clear hy
  induction t using Int.induction_on with
  | zero => simpa using h0
  | succ n ih =>
    rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]; exact h1 _ ih
  | pred n ih =>
    rw [sub_eq_neg_add, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv]
    exact h2 _ ih

lemma Skel.symm_pos (hs : Skel σ E) (y : ℤ) : 0 < σ.symm y ↔ 0 < y := by
  rw [← hs.pos, Equiv.apply_symm_apply]

lemma Skel.orbit_pos (hs : Skel σ E) {x : ℤ} (hx : 0 < x) :
    ∀ y ∈ permOrbit σ x, 0 < y :=
  permOrbit_induction (fun y => 0 < y) hx (fun y hy => (hs.pos y).2 hy)
    (fun y hy => (hs.symm_pos y).2 hy)

/-- After an `E`-point `e`, every point is above `e`, and every non-`E` point has an `E`
predecessor `≥ e`. -/
lemma Skel.after (hs : Skel σ E) {e : ℤ} (he0 : 0 < e) (he : E e) (n : ℕ) :
    e < (σ ^ (n + 1)) e ∧
      (E ((σ ^ (n + 1)) e) ∨ (E (σ.symm ((σ ^ (n + 1)) e)) ∧ e ≤ σ.symm ((σ ^ (n + 1)) e))) := by
  induction n with
  | zero =>
    simp only [zero_add, pow_one]
    refine ⟨hs.up e he0 he, ?_⟩
    by_cases h : E (σ e)
    · exact Or.inl h
    · exact Or.inr ⟨by simpa using he, by simp⟩
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    set z := (σ ^ (n + 1)) e with hz
    obtain ⟨hlt, hE | ⟨hw, hwe⟩⟩ := ih
    · have hup := hs.up z (by omega) hE
      refine ⟨by omega, ?_⟩
      by_cases h : E (σ z)
      · exact Or.inl h
      · exact Or.inr ⟨by simpa using hE, by simp; omega⟩
    · set w := σ.symm z with hw'
      have hzw : σ w = z := by simp [hw']
      by_cases hz' : E z
      · have hup := hs.up z (by omega) hz'
        refine ⟨by omega, ?_⟩
        by_cases h : E (σ z)
        · exact Or.inl h
        · exact Or.inr ⟨by simpa using hz', by simp; omega⟩
      · have h2 := hs.twoStep w (by omega) hw (by rw [hzw]; exact hz')
        rw [hzw] at h2
        exact ⟨by omega, Or.inl h2.1⟩

lemma Skel.lt_pow (hs : Skel σ E) {e : ℤ} (he0 : 0 < e) (he : E e) (n : ℕ) :
    e < (σ ^ (n + 1)) e :=
  (hs.after he0 he n).1

/-- Before an entry point every point is outside `E` and above it. -/
lemma Skel.before (hs : Skel σ E) {e : ℤ} (he : SkEntry σ E e) (n : ℕ) :
    ¬E ((σ⁻¹ ^ (n + 1)) e) ∧ e < (σ⁻¹ ^ (n + 1)) e := by
  obtain ⟨he0, heE, h1, h2⟩ := he
  have hnE : ∀ n : ℕ, ¬E ((σ⁻¹ ^ (n + 1)) e) := by
    intro n
    cases n with
    | zero => simpa using h1
    | succ m =>
      intro hw
      set w := (σ⁻¹ ^ (m + 1 + 1)) e with hw'
      have hw0 : 0 < w := hs.orbit_pos he0 _ ⟨-((m + 1 + 1 : ℕ) : ℤ), by
        dsimp only; rw [hw', zpow_neg, zpow_natCast, inv_pow]⟩
      have hback : (σ ^ (m + 1)) w = σ.symm e := by
        rw [hw', pow_succ σ⁻¹ (m + 1), Equiv.Perm.mul_apply, inv_pow,
          Equiv.Perm.coe_inv (σ ^ (m + 1)), Equiv.apply_symm_apply, Equiv.Perm.coe_inv]
      obtain ⟨-, hE | ⟨hE, -⟩⟩ := hs.after hw0 hw m
      · rw [hback] at hE; exact h1 hE
      · rw [hback] at hE; exact h2 hE
  refine ⟨hnE n, ?_⟩
  induction n with
  | zero =>
    simp only [zero_add, pow_one, Equiv.Perm.coe_inv]
    have hp0 : 0 < σ.symm e := (hs.symm_pos e).2 he0
    have := hs.down _ hp0 h1
    rw [Equiv.apply_symm_apply] at this
    rcases this.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ heE) h1
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.coe_inv]
    set p := (σ⁻¹ ^ (n + 1)) e
    have hp0 : 0 < σ.symm p := (hs.symm_pos p).2 (by omega)
    have hnE' := hnE (n + 1)
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.coe_inv] at hnE'
    have := hs.down _ hp0 hnE'
    rw [Equiv.apply_symm_apply] at this
    omega

/-- An entry point is strictly below every other point of its orbit. -/
lemma Skel.entry_lt (hs : Skel σ E) {e y : ℤ} (he : SkEntry σ E e) (hy : y ∈ permOrbit σ e)
    (hne : y ≠ e) : e < y := by
  obtain ⟨t, rfl⟩ := mem_permOrbit_iff.1 hy
  rcases Int.eq_nat_or_neg t with ⟨n, rfl | rfl⟩
  · cases n with
    | zero => simp at hne
    | succ m => rw [zpow_natCast]; exact hs.lt_pow he.1 he.2.1 m
  · cases n with
    | zero => simp at hne
    | succ m =>
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      exact (hs.before he m).2

/-- A minimum of the orbit of a non-fixed `x > 0` is an entry point. -/
lemma Skel.entry_of_min (hs : Skel σ E) {x m : ℤ} (hx : 0 < x) (hfix : σ x ≠ x)
    (hm : m ∈ permOrbit σ x) (hmin : ∀ y ∈ permOrbit σ x, m ≤ y) : SkEntry σ E m := by
  have hpos := hs.orbit_pos hx
  have hm0 := hpos m hm
  have hmfix : σ m ≠ m := by
    intro h
    obtain ⟨t, ht⟩ := mem_permOrbit_iff.1 hm
    have := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h (-t)
    rw [← ht] at this
    rw [← Equiv.Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Equiv.Perm.one_apply,
      ht] at this
    exact hfix (by rw [this]; exact h)
  have hE : E m := by
    by_contra h
    have h1 := hs.down m hm0 h
    have h2 := hmin _ (apply_mem_permOrbit hm)
    exact hmfix (le_antisymm h1 h2)
  have hm1 := symm_mem_permOrbit hm
  have hm2 := symm_mem_permOrbit hm1
  refine ⟨hm0, hE, fun h => ?_, fun h => ?_⟩
  · have := hs.up _ (hpos _ hm1) h
    rw [Equiv.apply_symm_apply] at this
    have := hmin _ hm1
    omega
  · have hnE : ¬E (σ (σ.symm (σ.symm m))) := by
      rw [Equiv.apply_symm_apply]
      intro h'
      have := hs.up _ (hpos _ hm1) h'
      rw [Equiv.apply_symm_apply] at this
      have := hmin _ hm1
      omega
    have := (hs.twoStep _ (hpos _ hm2) h hnE).2
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    have := hmin _ hm2
    omega

/-- Orbits in `ℕ⁺` have a minimum. -/
lemma Skel.exists_min (hs : Skel σ E) {x : ℤ} (hx : 0 < x) :
    ∃ m ∈ permOrbit σ x, ∀ y ∈ permOrbit σ x, m ≤ y := by
  have hpos := hs.orbit_pos hx
  have hex : ∃ n : ℕ, ∃ y ∈ permOrbit σ x, y = n := ⟨x.toNat, x, mem_permOrbit_self x, by omega⟩
  classical
  obtain ⟨y, hy, hyn⟩ := Nat.find_spec hex
  refine ⟨y, hy, fun z hz => ?_⟩
  have := Nat.find_min' hex ⟨z, hz, (Int.toNat_of_nonneg (hpos z hz).le).symm⟩
  have := hpos z hz
  omega

/-- The orbit of a non-fixed `x > 0` has exactly one entry point. -/
lemma Skel.existsUnique_entry (hs : Skel σ E) {x : ℤ} (hx : 0 < x) (hfix : σ x ≠ x) :
    ∃! e, SkEntry σ E e ∧ e ∈ permOrbit σ x := by
  obtain ⟨m, hm, hmin⟩ := hs.exists_min hx
  refine ⟨m, ⟨hs.entry_of_min hx hfix hm hmin, hm⟩, fun e ⟨he, hex⟩ => ?_⟩
  by_contra hne
  have h1 := hs.entry_lt he (by rw [permOrbit_eq_of_mem hex]; exact hm) (Ne.symm hne)
  have h2 := hmin e hex
  omega

/-- The orbit of a non-fixed `x > 0` is not periodic: `t ↦ σ^t x` is injective. -/
lemma Skel.zpow_injective (hs : Skel σ E) {x : ℤ} (hx : 0 < x) (hfix : σ x ≠ x) :
    Function.Injective fun t : ℤ => (σ ^ t) x := by
  obtain ⟨m, hm, hmin⟩ := hs.exists_min hx
  have he := hs.entry_of_min hx hfix hm hmin
  obtain ⟨c, rfl⟩ := mem_permOrbit_iff.1 hm
  have key : ∀ a b : ℤ, a < b → (σ ^ a) ((σ ^ c) x) ≠ (σ ^ b) ((σ ^ c) x) := by
    intro a b hab h
    have hper : (σ ^ (b - a)) ((σ ^ c) x) = (σ ^ c) x := by
      rw [show b - a = -a + b by ring, zpow_add, Equiv.Perm.mul_apply, ← h,
        ← Equiv.Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Equiv.Perm.one_apply]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b - a = (n + 1 : ℕ) := ⟨(b - a - 1).toNat, by omega⟩
    rw [hn, zpow_natCast] at hper
    have := hs.lt_pow he.1 he.2.1 n
    omega
  intro a b h
  dsimp only at h
  have h' : (σ ^ (a - c)) ((σ ^ c) x) = (σ ^ (b - c)) ((σ ^ c) x) := by
    rw [← Equiv.Perm.mul_apply, ← zpow_add, sub_add_cancel, ← Equiv.Perm.mul_apply,
      ← zpow_add, sub_add_cancel, h]
  rcases lt_trichotomy (a - c) (b - c) with hlt | heq | hgt
  · exact absurd h' (key _ _ hlt)
  · omega
  · exact absurd h'.symm (key _ _ hgt)

/-- An injective sequence of positive integers tends to `∞`. -/
lemma tendsto_atTop_of_injective_pos {f : ℕ → ℤ} (hf : Function.Injective f)
    (hpos : ∀ n, 0 < f n) : Tendsto f atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hfin : {n | f n < b}.Finite :=
    ((Set.finite_Ioo 0 b).preimage hf.injOn).subset fun n hn => ⟨hpos n, hn⟩
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine Filter.eventually_atTop.2 ⟨N + 1, fun n hn => not_lt.mp fun h => ?_⟩
  have := hN h
  omega

lemma Skel.permOrbit_infinite (hs : Skel σ E) {x : ℤ} (hx : 0 < x) (hfix : σ x ≠ x) :
    (permOrbit σ x).Infinite :=
  Set.infinite_range_of_injective (hs.zpow_injective hx hfix)

lemma Skel.tendsto_pow (hs : Skel σ E) {x : ℤ} (hx : 0 < x) (hfix : σ x ≠ x) :
    Tendsto (fun n : ℕ => (σ ^ n) x) atTop atTop := by
  refine tendsto_atTop_of_injective_pos (fun a b h => ?_) fun n => ?_
  · have := hs.zpow_injective hx hfix (a₁ := a) (a₂ := b) (by simpa [zpow_natCast] using h)
    omega
  · exact hs.orbit_pos hx _ ⟨n, by simp [zpow_natCast]⟩

lemma Skel.tendsto_pow_neg (hs : Skel σ E) {x : ℤ} (hx : 0 < x) (hfix : σ x ≠ x) :
    Tendsto (fun n : ℕ => (σ ^ (-(n : ℤ))) x) atTop atTop := by
  refine tendsto_atTop_of_injective_pos (fun a b h => ?_) fun n => ?_
  · have := hs.zpow_injective hx hfix h
    omega
  · exact hs.orbit_pos hx _ (zpow_mem_permOrbit x _)

end Skeleton

/-- Entry points: even `y > 0` with an odd preimage (`y = ⌊jβ⌋`) that is not `2rk` for a `k`
with `W(2k)` odd (the only way the second preimage is even, by Theorem D). -/
def IsEntry (r : ℕ) (y : ℤ) : Prop :=
  0 < y ∧ y % 2 = 0 ∧ (∃ j : ℤ, wq r (2 * j - 1) = y) ∧
    ∀ k : ℤ, wq r (2 * k) % 2 = 1 → 2 * r * k ≠ y

/-- `W` satisfies the skeleton hypotheses with the evens as the climbing class. -/
lemma wq_skel (hr : 2 ≤ r) : Skel (wqPerm r hr) fun y => y % 2 = 0 where
  pos y := wq_pos_iff hr y
  up y hy he := by
    obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k := ⟨y / 2, by omega⟩
    have := (wq_two_mul_bounds hr (show 1 ≤ k by omega)).1
    rw [wqPerm_apply]
    have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
    nlinarith
  twoStep y hy he hne := by
    obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k := ⟨y / 2, by omega⟩
    simp only [wqPerm_apply] at hne ⊢
    rw [wq_wq_of_odd hr k (by omega)]
    have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
    refine ⟨by rw [mul_assoc]; exact Int.mul_emod_right _ _, by nlinarith⟩
  down y hy he := by
    obtain ⟨j, rfl⟩ : ∃ j, y = 2 * j - 1 := ⟨(y + 1) / 2, by omega⟩
    rw [wqPerm_apply]
    rcases eq_or_lt_of_le (show 1 ≤ j by omega) with rfl | hj
    · rw [show (2 : ℤ) * 1 - 1 = 1 by norm_num, wq_one hr]
    · exact ((wq_two_mul_sub_one_bounds hr (show 1 ≤ j by omega)).2 (by omega)).le

/-- The only positive fixed point of `W` is `1`. -/
lemma wq_ne_self (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) : wqPerm r hr x ≠ x := by
  rw [wqPerm_apply]
  obtain ⟨k, rfl | rfl⟩ : ∃ k, x = 2 * k ∨ x = 2 * k - 1 := ⟨(x + 1) / 2, by omega⟩
  · have := (wq_two_mul_bounds hr (show 1 ≤ k by omega)).1
    have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
    intro h; nlinarith
  · exact ((wq_two_mul_sub_one_bounds hr (show 1 ≤ k by omega)).2 (by omega)).ne

/-- **(ratified).**  The paper's form: `y` is an entry point iff it is even and positive with
`W⁻¹(y)` and `W⁻²(y)` odd.  Paper proof: `W⁻¹ y` is odd iff `y ∈ W(odd)`; if it is odd and
`W⁻² y = 2k` is even, Theorem D gives `y = 2rk`; conversely `y = 2rk` with `W(2k)` odd has
`W⁻¹ y = W(2k)`, `W⁻² y = 2k`. -/
theorem isEntry_iff (hr : 2 ≤ r) (y : ℤ) :
    IsEntry r y ↔ 0 < y ∧ y % 2 = 0 ∧ (wqPerm r hr).symm y % 2 = 1 ∧
      (wqPerm r hr).symm ((wqPerm r hr).symm y) % 2 = 1 := by
  set σ := wqPerm r hr with hσ
  constructor
  · rintro ⟨h0, h2, ⟨j, hj⟩, hk⟩
    have hs1 : σ.symm y = 2 * j - 1 := by rw [Equiv.symm_apply_eq]; exact hj.symm
    refine ⟨h0, h2, by rw [hs1]; omega, ?_⟩
    rw [hs1]
    by_contra hodd
    obtain ⟨k, hk2⟩ : ∃ k, σ.symm (2 * j - 1) = 2 * k := ⟨σ.symm (2 * j - 1) / 2, by omega⟩
    have hwk : wq r (2 * k) = 2 * j - 1 := by
      rw [← wqPerm_apply hr, ← hk2]; exact σ.apply_symm_apply _
    refine hk k (by rw [hwk]; omega) ?_
    rw [← wq_wq_of_odd hr k (by rw [hwk]; omega), hwk, hj]
  · rintro ⟨h0, h2, h3, h4⟩
    refine ⟨h0, h2, ⟨(σ.symm y + 1) / 2, ?_⟩, fun k hk hy => ?_⟩
    · rw [show 2 * ((σ.symm y + 1) / 2) - 1 = σ.symm y by omega, ← wqPerm_apply hr]
      exact σ.apply_symm_apply y
    · have e1 : σ.symm y = wq r (2 * k) := by
        rw [Equiv.symm_apply_eq, wqPerm_apply, wq_wq_of_odd hr k hk, hy]
      have e2 : σ.symm (σ.symm y) = 2 * k := by
        rw [e1, Equiv.symm_apply_eq, wqPerm_apply]
      rw [e2] at h4
      omega

lemma isEntry_iff_skEntry (hr : 2 ≤ r) (y : ℤ) :
    IsEntry r y ↔ SkEntry (wqPerm r hr) (fun y => y % 2 = 0) y := by
  rw [isEntry_iff hr]
  unfold SkEntry
  constructor <;> rintro ⟨a, b, c, d⟩ <;> exact ⟨a, b, by omega, by omega⟩

/-- **(ratified).**  Orbits of positive points stay positive. -/
theorem permOrbit_subset_pos (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    permOrbit (wqPerm r hr) x ⊆ {y | 0 < y} := by
  exact fun y hy => (wq_skel hr).orbit_pos hx y hy

/-- **(ratified).**  `{1}` is a finite orbit. -/
theorem permOrbit_wqPerm_one (hr : 2 ≤ r) : permOrbit (wqPerm r hr) 1 = {1} := by
  ext y
  constructor
  · intro hy
    obtain ⟨t, rfl⟩ := mem_permOrbit_iff.1 hy
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (wq_one hr) t
  · rintro rfl
    exact mem_permOrbit_self 1

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
  simp_rw [isEntry_iff_skEntry hr]
  exact (wq_skel hr).existsUnique_entry (by omega) (wq_ne_self hr hx)

/-- **(ratified, Theorem F, minimum).**  An entry point is strictly below every other point of
its orbit.  Paper proof: before `e` all points are odd and increase backward (c); after `e` the
even points increase (a) and each odd point is `W(2k) > 2k ≥ e`. -/
theorem isEntry_lt_of_mem_orbit (hr : 2 ≤ r) {e y : ℤ} (he : IsEntry r e)
    (hy : y ∈ permOrbit (wqPerm r hr) e) (hne : y ≠ e) : e < y := by
  exact (wq_skel hr).entry_lt ((isEntry_iff_skEntry hr e).1 he) hy hne

/-- **(ratified, Theorem F, no other finite orbit).**  Every orbit through `x > 1` is
infinite. -/
theorem permOrbit_wqPerm_infinite (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    (permOrbit (wqPerm r hr) x).Infinite := by
  exact (wq_skel hr).permOrbit_infinite (by omega) (wq_ne_self hr hx)

/-- **(ratified, Theorem F, forward escape).**  For `x > 1` the forward orbit tends to `∞`. -/
theorem tendsto_wqPerm_pow (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => (wqPerm r hr ^ n) x) atTop atTop := by
  exact (wq_skel hr).tendsto_pow (by omega) (wq_ne_self hr hx)

/-- **(ratified, Theorem F, backward escape).**  For `x > 1` the backward orbit tends to `∞`. -/
theorem tendsto_wqPerm_pow_neg (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => (wqPerm r hr ^ (-(n : ℤ))) x) atTop atTop := by
  exact (wq_skel hr).tendsto_pow_neg (by omega) (wq_ne_self hr hx)

/-- **(ratified, Theorem F, orbit minima).**  For `x > 0`: `x` is the minimum of its orbit iff
`x = 1` or `x` is an entry point. -/
theorem isOrbitMin_iff (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    (∀ y ∈ permOrbit (wqPerm r hr) x, x ≤ y) ↔ x = 1 ∨ IsEntry r x := by
  constructor
  · intro hmin
    rcases eq_or_lt_of_le (show 1 ≤ x by omega) with h | h
    · exact Or.inl h.symm
    · exact Or.inr ((isEntry_iff_skEntry hr x).2
        ((wq_skel hr).entry_of_min hx (wq_ne_self hr h) (mem_permOrbit_self x) hmin))
  · rintro (rfl | he) y hy
    · rw [permOrbit_wqPerm_one hr] at hy
      rw [Set.mem_singleton_iff.1 hy]
    · by_cases h : y = x
      · rw [h]
      · exact (isEntry_lt_of_mem_orbit hr he hy h).le

/-- **(ratified, Theorem F, indexing).**  The orbits meeting `ℕ⁺` are indexed by `{1}` and the
entry points. -/
theorem permOrbit_bijOn (hr : 2 ≤ r) :
    Set.BijOn (permOrbit (wqPerm r hr)) ({1} ∪ {y | IsEntry r y})
      {O | ∃ x : ℤ, 0 < x ∧ O = permOrbit (wqPerm r hr) x} := by
  have hmin : ∀ z ∈ ({1} ∪ {y | IsEntry r y} : Set ℤ),
      0 < z ∧ ∀ y ∈ permOrbit (wqPerm r hr) z, z ≤ y := by
    intro z hz
    have hz0 : 0 < z := by
      rcases hz with hz | hz
      · rw [Set.mem_singleton_iff.1 hz]; norm_num
      · exact hz.1
    refine ⟨hz0, (isOrbitMin_iff hr hz0).2 ?_⟩
    rcases hz with hz | hz
    · exact Or.inl (Set.mem_singleton_iff.1 hz)
    · exact Or.inr hz
  refine ⟨fun z hz => ⟨z, (hmin z hz).1, rfl⟩, fun a ha b hb hab => ?_, ?_⟩
  · have h1 := (hmin a ha).2 b (by rw [hab]; exact mem_permOrbit_self b)
    have h2 := (hmin b hb).2 a (by rw [← hab]; exact mem_permOrbit_self a)
    exact le_antisymm h1 h2
  · rintro O ⟨x, hx, rfl⟩
    rcases eq_or_lt_of_le (show 1 ≤ x by omega) with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]⟩
    · obtain ⟨e, ⟨he, hem⟩, -⟩ := existsUnique_isEntry_mem_orbit hr h
      exact ⟨e, Or.inr he, permOrbit_eq_of_mem hem⟩

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

/-- `A(X)` counts the even `y ∈ [1, X]` in the odd branch. -/
lemma countA_eq (hr : 2 ≤ r) (X : ℕ) [DecidablePred fun y : ℤ =>
      y % 2 = 0 ∧ ∃ j : ℤ, wq r (2 * j - 1) = y] :
    countA r X = ((Finset.Icc (1 : ℤ) X).filter fun y =>
      y % 2 = 0 ∧ ∃ j : ℤ, wq r (2 * j - 1) = y).card := by
  unfold countA
  apply Finset.card_nbij (fun j : ℕ => wq r (2 * (j : ℤ) - 1))
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hj ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hj
    have := (wq_two_mul_sub_one_bounds hr (show (1 : ℤ) ≤ j by exact_mod_cast h1)).1
    exact ⟨⟨by omega, h3⟩, h4, j, rfl⟩
  · intro a _ b _ h
    have := (wq_odd_strictMono hr).injective h
    exact_mod_cast this
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hy
    obtain ⟨⟨h1, h2⟩, h3, j, rfl⟩ := hy
    have hj1 : 1 ≤ j := by
      by_contra h
      have := (wq_pos_iff hr (2 * j - 1)).1 (by omega)
      omega
    have := (wq_two_mul_sub_one_bounds hr hj1).1
    refine ⟨j.toNat, ?_, ?_⟩
    · simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq,
        Int.toNat_of_nonneg (show 0 ≤ j by omega)]
      exact ⟨⟨by omega, by omega⟩, h2, h3⟩
    · simp only [Int.toNat_of_nonneg (show 0 ≤ j by omega)]

/-- `B(X)` counts the `2rk ∈ [1, X]` with `W(2k)` odd. -/
lemma countB_eq (hr : 2 ≤ r) (X : ℕ) [DecidablePred fun y : ℤ =>
      ∃ k : ℤ, wq r (2 * k) % 2 = 1 ∧ 2 * r * k = y] :
    countB r X = ((Finset.Icc (1 : ℤ) X).filter fun y =>
      ∃ k : ℤ, wq r (2 * k) % 2 = 1 ∧ 2 * r * k = y).card := by
  unfold countB
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  apply Finset.card_nbij (fun k : ℕ => 2 * (r : ℤ) * k)
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hk ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hk
    have h1' : (1 : ℤ) ≤ k := by exact_mod_cast h1
    have h3' : 2 * (r : ℤ) * k ≤ X := by exact_mod_cast h3
    exact ⟨⟨by nlinarith, h3'⟩, k, h4, rfl⟩
  · intro a _ b _ h
    have : (a : ℤ) = b := by
      have h' : (2 * (r : ℤ)) * a = (2 * r) * b := h
      exact mul_left_cancel₀ (by omega) h'
    exact_mod_cast this
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hy
    obtain ⟨⟨h1, h2⟩, k, h3, rfl⟩ := hy
    have hk1 : 1 ≤ k := by
      by_contra h
      nlinarith
    have hkX : k ≤ X := by nlinarith
    refine ⟨k.toNat, ?_, ?_⟩
    · simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq,
        Int.toNat_of_nonneg (show 0 ≤ k by omega)]
      refine ⟨⟨by omega, by omega⟩, ?_, h3⟩
      have : ((2 * r * k.toNat : ℕ) : ℤ) ≤ X := by
        push_cast; rw [Int.toNat_of_nonneg (by omega)]; exact h2
      exact_mod_cast this
    · simp only [Int.toNat_of_nonneg (show 0 ≤ k by omega)]

/-- **(ratified, Theorem F, exact count).**  `#{orbit minima ≤ X} = 1 + A(X) − B(X)`.  Paper
proof: by `isOrbitMin_iff` the minima in `[1, X]` are `1` and the entry points `≤ X`.  The even
`y ≤ X` in `W(odd)` are the even `⌊jβ⌋ ≤ X` (`A(X)`); among them the `2rk` with `W(2k)` odd
(`B(X)`, an injective image of `k`) are exactly the non-entries. -/
theorem minCount_add_countB (hr : 2 ≤ r) {X : ℕ} (hX : 1 ≤ X) :
    minCount r hr X + countB r X = 1 + countA r X := by
  classical
  set S := Finset.Icc (1 : ℤ) X with hS
  rw [countA_eq hr X, countB_eq hr X]
  have hBA : ∀ y, (∃ k : ℤ, wq r (2 * k) % 2 = 1 ∧ 2 * r * k = y) →
      y % 2 = 0 ∧ ∃ j : ℤ, wq r (2 * j - 1) = y := by
    rintro y ⟨k, hk, rfl⟩
    refine ⟨by rw [mul_assoc]; exact Int.mul_emod_right _ _, (wq r (2 * k) + 1) / 2, ?_⟩
    rw [show 2 * ((wq r (2 * k) + 1) / 2) - 1 = wq r (2 * k) by omega, wq_wq_of_odd hr k hk]
  have hsplitA := Finset.card_filter_add_card_filter_not
    (s := S.filter fun y => y % 2 = 0 ∧ ∃ j : ℤ, wq r (2 * j - 1) = y)
    (fun y => ∃ k : ℤ, wq r (2 * k) % 2 = 1 ∧ 2 * r * k = y)
  have e1 : ((S.filter fun y => y % 2 = 0 ∧ ∃ j : ℤ, wq r (2 * j - 1) = y).filter
      fun y => ∃ k : ℤ, wq r (2 * k) % 2 = 1 ∧ 2 * r * k = y) =
      S.filter fun y => ∃ k : ℤ, wq r (2 * k) % 2 = 1 ∧ 2 * r * k = y := by
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, hBA y h3⟩, h3⟩
  have hsplitM := Finset.card_filter_add_card_filter_not
    (s := S.filter fun x => ∀ y ∈ permOrbit (wqPerm r hr) x, x ≤ y) (fun y => y = 1)
  have e2 : ((S.filter fun x => ∀ y ∈ permOrbit (wqPerm r hr) x, x ≤ y).filter
      fun y => y = 1) = {1} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton, hS, Finset.mem_Icc]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro rfl
      exact ⟨⟨⟨le_rfl, by exact_mod_cast hX⟩, (isOrbitMin_iff hr one_pos).2 (Or.inl rfl)⟩, rfl⟩
  have e3 : ((S.filter fun x => ∀ y ∈ permOrbit (wqPerm r hr) x, x ≤ y).filter
      fun y => ¬y = 1) = ((S.filter fun y => y % 2 = 0 ∧ ∃ j : ℤ, wq r (2 * j - 1) = y).filter
      fun y => ¬∃ k : ℤ, wq r (2 * k) % 2 = 1 ∧ 2 * r * k = y) := by
    ext y
    simp only [Finset.mem_filter, hS, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hy, hmin⟩, h1⟩
      rcases (isOrbitMin_iff hr (by omega)).1 hmin with h | ⟨-, h2, h3, h4⟩
      · exact absurd h h1
      · exact ⟨⟨hy, h2, h3⟩, fun ⟨k, hk, hky⟩ => h4 k hk hky⟩
    · rintro ⟨⟨hy, h2, h3⟩, h4⟩
      refine ⟨⟨hy, (isOrbitMin_iff hr (by omega)).2
        (Or.inr ⟨by omega, h2, h3, fun k hk hky => h4 ⟨k, hk, hky⟩⟩)⟩, by omega⟩
  unfold minCount
  rw [← hsplitA, e1, ← hsplitM, e2, e3, Finset.card_singleton]
  ring

/-- There are `⌊X/2⌋` even integers in `[1, X]`. -/
lemma card_filter_even (X : ℕ) :
    ((Finset.Icc (1 : ℤ) X).filter fun y => y % 2 = 0).card = X / 2 := by
  rw [show X / 2 = (Finset.Icc 1 (X / 2)).card by simp]
  symm
  apply Finset.card_nbij (fun j : ℕ => 2 * (j : ℤ))
  · intro j hj
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.coe_filter, Finset.mem_Icc,
      Set.mem_ofPred_eq] at hj ⊢
    omega
  · intro a _ b _ h
    have : (a : ℤ) = b := by simp only at h; omega
    exact_mod_cast this
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hy
    refine ⟨(y / 2).toNat, ?_, ?_⟩
    · simp only [Finset.coe_Icc, Set.mem_Icc]; omega
    · simp only; omega

/-- `B(X) ≤ ⌊X/2r⌋`. -/
lemma countB_le (hr : 2 ≤ r) (X : ℕ) : countB r X ≤ X / (2 * r) := by
  unfold countB
  calc _ ≤ (Finset.Icc 1 (X / (2 * r))).card := by
          apply Finset.card_le_card
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
          refine ⟨hk.1.1, (Nat.le_div_iff_mul_le (by omega)).2 ?_⟩
          nlinarith [hk.2.1]
    _ = X / (2 * r) := by simp

/-- `#{k ≥ 1 : W(2k) ≤ X} ≤ ⌊X/(4r − 2)⌋`. -/
lemma card_even_branch_le (hr : 2 ≤ r) (X : ℕ) [DecidablePred fun y : ℤ =>
      ∃ k : ℤ, wq r (2 * k) = y] :
    ((Finset.Icc (1 : ℤ) X).filter fun y => ∃ k : ℤ, wq r (2 * k) = y).card ≤
      X / (4 * r - 2) := by
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  calc _ ≤ ((Finset.Icc 1 (X / (4 * r - 2))).image fun k : ℕ => wq r (2 * (k : ℤ))).card := by
          apply Finset.card_le_card
          intro y hy
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at hy ⊢
          obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hy
          have hk : 1 ≤ k := by
            by_contra h
            have := (wq_pos_iff hr (2 * k)).1 (by omega)
            omega
          have hb := (wq_two_mul_bounds hr hk).1
          refine ⟨k.toNat, ⟨by omega, (Nat.le_div_iff_mul_le (by omega)).2 ?_⟩, by
            rw [Int.toNat_of_nonneg (by omega)]⟩
          have : ((k.toNat * (4 * r - 2) : ℕ) : ℤ) ≤ X := by
            push_cast [Nat.cast_sub (show 2 ≤ 4 * r by omega)]
            rw [Int.toNat_of_nonneg (by omega)]
            nlinarith
          exact_mod_cast this
    _ ≤ (Finset.Icc 1 (X / (4 * r - 2))).card := Finset.card_image_le
    _ = X / (4 * r - 2) := by simp

/-- `A(X) ≥ ⌊X/2⌋ − ⌊X/(4r − 2)⌋`: every even `y ∈ [1, X]` is in one of the two branches. -/
lemma countA_ge (hr : 2 ≤ r) (X : ℕ) : X / 2 ≤ countA r X + X / (4 * r - 2) := by
  classical
  rw [countA_eq hr X, ← card_filter_even X]
  refine (Finset.card_le_card ?_).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (card_even_branch_le hr X) _))
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_union] at hy ⊢
  obtain ⟨n, hn⟩ := (wq_bijective hr).2 y
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k - 1 := ⟨(n + 1) / 2, by omega⟩
  · exact Or.inr ⟨hy.1, k, hn⟩
  · exact Or.inl ⟨hy.1, hy.2, k, hn⟩

/-- **(ratified, Theorem F, unconditional lower bound).**
`#{orbit minima ≤ X} ≥ 1 + ⌊X/2⌋ − ⌊X/(4r − 2)⌋ − ⌊X/2r⌋`, linear in `X` (`≥ X/12`).
Paper proof: `A(X) = #{even y ≤ X} − #{even ⌊kα⌋ ≤ X} ≥ ⌊X/2⌋ − ⌊X/(4r − 2)⌋` by
`wq_two_mul_bounds`, and `B(X) ≤ ⌊X/2r⌋`. -/
theorem minCount_ge (hr : 2 ≤ r) {X : ℕ} (hX : 1 ≤ X) :
    1 + (X : ℤ) / 2 - X / (4 * r - 2) - X / (2 * r) ≤ minCount r hr X := by
  have h := minCount_add_countB hr hX
  have hA := countA_ge hr X
  have hB := countB_le hr X
  have c1 : ((X / (4 * r - 2) : ℕ) : ℤ) = (X : ℤ) / (4 * r - 2) := by
    rw [Int.natCast_div]; congr 1; omega
  have c2 : ((X / (2 * r) : ℕ) : ℤ) = (X : ℤ) / (2 * r) := by
    rw [Int.natCast_div]; push_cast; ring
  have c3 : ((X / 2 : ℕ) : ℤ) = (X : ℤ) / 2 := by
    rw [Int.natCast_div]; push_cast; ring
  rw [← c1, ← c2, ← c3]
  omega

/-- **(ratified).**  Every minimum other than `1` is even. -/
theorem minCount_le (hr : 2 ≤ r) (X : ℕ) : minCount r hr X ≤ 1 + X / 2 := by
  classical
  unfold minCount
  calc _ ≤ (insert 1 ((Finset.Icc (1 : ℤ) X).filter fun y => y % 2 = 0)).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_Icc] at hx ⊢
          rcases (isOrbitMin_iff hr (by omega)).1 hx.2 with h | h
          · exact Or.inl h
          · exact Or.inr ⟨hx.1, h.2.1⟩
    _ ≤ _ := (Finset.card_insert_le _ _).trans (by rw [card_filter_even]; omega)

/-- **(ratified, Theorem F, conclusion).**  `W_α` has infinitely many infinite orbits.  Paper
proof: `C = 2ℤ ∪ W(2ℤ)` is a trap (`W(2k)` even stays in `2ℤ`; `W(2k)` odd maps to `2rk`), its
entry points `C ∖ W(C)` are the even `y` with `W⁻¹ y, W⁻² y` odd (`isEntry_iff`), and they are
infinitely many by `minCount_ge` below (or apply `permOrbit_bijOn` and
`permOrbit_wqPerm_infinite`). -/
theorem wqPerm_infinitelyManyInfiniteOrbits (hr : 2 ≤ r) :
    InfinitelyManyInfiniteOrbits (wqPerm r hr) := by
  have hE : {y | IsEntry r y}.Infinite := by
    intro hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    set N := B.toNat + 2 with hN
    have hX : 1 ≤ 12 * N := by omega
    have hge := minCount_ge hr hX
    have hle : minCount r hr (12 * N) ≤ B.toNat + 1 := by
      classical
      unfold minCount
      calc _ ≤ (Finset.Icc (1 : ℤ) (B.toNat + 1)).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
              obtain ⟨⟨h1, h2⟩, h3⟩ := hx
              rcases (isOrbitMin_iff hr (by omega)).1 h3 with rfl | he
              · omega
              · have := hB he; omega
        _ = B.toNat + 1 := by simp; omega
    have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
    set d := ((12 * N : ℕ) : ℤ) / (4 * r - 2) with hd
    set e := ((12 * N : ℕ) : ℤ) / (2 * r) with he
    have d0 : 0 ≤ d := Int.ediv_nonneg (by positivity) (by omega)
    have d1 : d * (4 * r - 2) ≤ ((12 * N : ℕ) : ℤ) := Int.ediv_mul_le _ (by omega)
    have e0 : 0 ≤ e := Int.ediv_nonneg (by positivity) (by omega)
    have e1 : e * (2 * r) ≤ ((12 * N : ℕ) : ℤ) := Int.ediv_mul_le _ (by omega)
    have d2 : d ≤ 2 * N := by push_cast at d1; nlinarith
    have e2 : e ≤ 3 * N := by push_cast at e1; nlinarith
    have h2 : ((12 * N : ℕ) : ℤ) / 2 = 6 * N := by push_cast; omega
    rw [h2] at hge
    have : (minCount r hr (12 * N) : ℤ) ≤ B.toNat + 1 := by exact_mod_cast hle
    omega
  have hinj : Set.InjOn (permOrbit (wqPerm r hr)) {y | IsEntry r y} :=
    (permOrbit_bijOn hr).injOn.mono Set.subset_union_right
  refine (hE.image hinj).mono ?_
  rintro _ ⟨e, he, rfl⟩
  refine ⟨e, he.1.le, rfl, permOrbit_wqPerm_infinite hr ?_⟩
  have := he.1
  have := he.2.1
  omega

/-- **Literature hypothesis (Bohl, Sierpiński, Weyl 1909-1916; not in Mathlib).**
`k√(r² − r)` is equidistributed mod 1, so `⌊2k√(r² − r)⌋` is odd (`{k√(r² − r)} ≥ 1/2`) for a
set of `k` of density `1/2`.  True for every `r ≥ 2` since `√(r² − r)` is irrational. -/
def SflOddDensityHalf (r : ℕ) : Prop :=
  Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter fun k : ℕ => sfl r k % 2 = 1).card : ℝ) / N)
    atTop (𝓝 (1 / 2))

/-- A count `g X` pinned between `(X + a)/c − 1` and `(X + a)/c` tends to `∞` and has
`g X / X → 1/c`. -/
lemma tendsto_ratio_of_bounds {g : ℕ → ℕ} {a c : ℝ} (hc : 0 < c)
    (hlo : ∀ X : ℕ, ((X : ℝ) + a) / c ≤ g X + 1) (hhi : ∀ X : ℕ, (g X : ℝ) ≤ ((X : ℝ) + a) / c) :
    Tendsto g atTop atTop ∧ Tendsto (fun X : ℕ => (g X : ℝ) / X) atTop (𝓝 (1 / c)) := by
  constructor
  · have h1 : Tendsto (fun X : ℕ => ((X : ℝ) + a) / c) atTop atTop :=
      (tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop).atTop_div_const hc
    have h2 : Tendsto (fun X : ℕ => (g X : ℝ) + 1) atTop atTop := tendsto_atTop_mono hlo h1
    have h3 := tendsto_atTop_add_const_right _ (-1) h2
    simp only [add_neg_cancel_right] at h3
    exact tendsto_natCast_atTop_iff.1 h3
  · have hz : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hl : Tendsto (fun X : ℕ => 1 / c + (a / c - 1) * (1 / (X : ℝ))) atTop (𝓝 (1 / c)) := by
      have := (tendsto_const_nhds (x := 1 / c)).add (hz.const_mul (a / c - 1))
      rwa [mul_zero, add_zero] at this
    have hu : Tendsto (fun X : ℕ => 1 / c + a / c * (1 / (X : ℝ))) atTop (𝓝 (1 / c)) := by
      have := (tendsto_const_nhds (x := 1 / c)).add (hz.const_mul (a / c))
      rwa [mul_zero, add_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with X hX
      have hX' : (0 : ℝ) < X := by exact_mod_cast hX
      rw [le_div_iff₀ hX']
      have e : (1 / c + (a / c - 1) * (1 / (X : ℝ))) * X = ((X : ℝ) + a) / c - 1 := by
        field_simp; ring
      rw [e]; linarith [hlo X]
    · filter_upwards [eventually_ge_atTop 1] with X hX
      have hX' : (0 : ℝ) < X := by exact_mod_cast hX
      rw [div_le_iff₀ hX']
      have e : (1 / c + a / c * (1 / (X : ℝ))) * X = ((X : ℝ) + a) / c := by
        field_simp
      rw [e]; exact hhi X

/-- Composing a density with a count of linear growth. -/
lemma tendsto_comp_ratio {F g : ℕ → ℕ} {d c : ℝ}
    (hF : Tendsto (fun N : ℕ => (F N : ℝ) / N) atTop (𝓝 d)) (hg : Tendsto g atTop atTop)
    (hgc : Tendsto (fun X : ℕ => (g X : ℝ) / X) atTop (𝓝 c)) :
    Tendsto (fun X : ℕ => (F (g X) : ℝ) / X) atTop (𝓝 (d * c)) := by
  refine ((hF.comp hg).mul hgc).congr' ?_
  filter_upwards [hg.eventually_ge_atTop 1, eventually_ge_atTop 1] with X h1 h2
  have h1' : (g X : ℝ) ≠ 0 := by positivity
  simp only [Function.comp]
  field_simp

/-- Real bounds for natural division. -/
lemma natDiv_bounds (n d : ℕ) (hd : 0 < d) :
    ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d ∧ (n : ℝ) / d ≤ ((n / d : ℕ) : ℝ) + 1 := by
  refine ⟨Nat.cast_div_le, ?_⟩
  have h := Nat.lt_mul_div_succ n hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hd']
  have : (n : ℝ) < d * ((n / d : ℕ) + 1 : ℕ) := by exact_mod_cast h
  push_cast at this
  linarith

/-- `#{k ∈ [1, N] : sfl r k odd}`. -/
def oddCount (r N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun k : ℕ => sfl r k % 2 = 1).card

/-- `W(2j − 1) ≤ X ⇔ jβ ≤ X + 1`. -/
lemma wq_odd_le_iff (hr : 2 ≤ r) (j X : ℤ) :
    wq r (2 * j - 1) ≤ X ↔ (j : ℝ) * betaQ r ≤ X + 1 := by
  rw [wq_two_mul_sub_one_eq_ceil hr, show ((X : ℝ) + 1) = ((X + 1 : ℤ) : ℝ) by push_cast; ring,
    ← Int.ceil_le]
  omega

/-- The number `J(X) = ⌊(X + 1)/β⌋` of `j ≥ 1` with `W(2j − 1) ≤ X`. -/
lemma le_floor_iff_wq (hr : 2 ≤ r) (j X : ℕ) :
    j ≤ ⌊((X : ℝ) + 1) / betaQ r⌋₊ ↔ wq r (2 * j - 1) ≤ X := by
  have hβ := (one_lt_betaQ_lt hr).1
  rw [Nat.le_floor_iff (by positivity), le_div_iff₀ (by linarith), wq_odd_le_iff hr]
  push_cast; rfl

lemma countA_eq_oddCount (hr : 2 ≤ r) (X : ℕ) :
    countA r X = oddCount r ⌊((X : ℝ) + 1) / betaQ r⌋₊ := by
  unfold countA oddCount
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc, le_floor_iff_wq hr]
  have hpar : wq r (2 * j - 1) % 2 = 0 ↔ sfl r j % 2 = 1 := by
    rw [wq_two_mul_sub_one, show (2 : ℤ) * r * j = 2 * (r * j) by ring]; omega
  rw [hpar]
  constructor
  · rintro ⟨⟨h1, -⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h4⟩
  · rintro ⟨⟨h1, h3⟩, h4⟩
    have := (wq_two_mul_sub_one_bounds hr (show (1 : ℤ) ≤ j by exact_mod_cast h1)).1
    exact ⟨⟨h1, by omega⟩, h3, h4⟩

lemma countB_eq_oddCount (hr : 2 ≤ r) (X : ℕ) :
    countB r X = oddCount r (X / (2 * r)) := by
  unfold countB oddCount
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  have hpar : wq r (2 * k) % 2 = 1 ↔ sfl r k % 2 = 1 := by
    rw [wq_two_mul, show (2 : ℤ) * r * k = 2 * (r * k) by ring]; omega
  rw [hpar, Nat.le_div_iff_mul_le (by omega)]
  constructor
  · rintro ⟨⟨h1, -⟩, h3, h4⟩; exact ⟨⟨h1, by linarith⟩, h4⟩
  · rintro ⟨⟨h1, h3⟩, h4⟩
    exact ⟨⟨h1, by nlinarith⟩, by linarith, h4⟩

/-- `J(X) = ⌊(X + 1)/β⌋ ∼ X/β`. -/
lemma tendsto_J (hr : 2 ≤ r) :
    Tendsto (fun X : ℕ => ⌊((X : ℝ) + 1) / betaQ r⌋₊) atTop atTop ∧
      Tendsto (fun X : ℕ => (⌊((X : ℝ) + 1) / betaQ r⌋₊ : ℝ) / X) atTop
        (𝓝 (1 / betaQ r)) := by
  have hβ := (one_lt_betaQ_lt hr).1
  refine tendsto_ratio_of_bounds (by linarith) (fun X => (Nat.lt_floor_add_one _).le)
    (fun X => Nat.floor_le (by positivity))

/-- `⌊(X + a)/2r⌋ ∼ X/2r`. -/
lemma tendsto_K (hr : 2 ≤ r) (a : ℕ) :
    Tendsto (fun X : ℕ => (X + a) / (2 * r)) atTop atTop ∧
      Tendsto (fun X : ℕ => (((X + a) / (2 * r) : ℕ) : ℝ) / X) atTop
        (𝓝 (1 / (2 * (r : ℝ)))) := by
  have hr' : (0 : ℝ) < 2 * r := by positivity
  refine tendsto_ratio_of_bounds (a := a) hr' (fun X => ?_) (fun X => ?_)
  · have := (natDiv_bounds (X + a) (2 * r) (by omega)).2
    push_cast at this ⊢; exact this
  · have := (natDiv_bounds (X + a) (2 * r) (by omega)).1
    push_cast at this ⊢; exact this

/-- The density value: `1/(2β) − 1/(4r) = (r − 1 + √(r² − r))/(4r)`. -/
lemma density_value (hr : 2 ≤ r) :
    1 / 2 * (1 / betaQ r) - 1 / 2 * (1 / (2 * (r : ℝ))) =
      ((r : ℝ) - 1 + √((r : ℝ) ^ 2 - r)) / (4 * r) := by
  have hβ := (one_lt_betaQ_lt hr).1
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr' : (0 : ℝ) < r := by linarith
  have h1 : 1 / betaQ r = (2 * r + 2 * √((r : ℝ) ^ 2 - r)) / (4 * r) := by
    rw [div_eq_div_iff (by linarith) (by positivity)]
    unfold betaQ
    linear_combination 4 * sqrt_sq_radicand r
  rw [h1]
  field_simp
  ring

/-- **(ratified, Theorem F, density, conditional on equidistribution).**  The orbit minima have
density `d_r = 1/(2β) − 1/(4r) = (r − 1 + √(r² − r))/(4r)`.  Paper proof: `⌊jβ⌋` is even iff
`sfl r j` is odd, and `⌊kα⌋` is odd iff `sfl r k` is odd; `A(X)` counts `j ≤ J(X) ∼ X/β`,
`B(X)` counts `k ≤ X/2r`; apply the hypothesis along `J(X)` and `⌊X/2r⌋`, and
`1/β = α/(4r)`. -/
theorem tendsto_minCount (hr : 2 ≤ r) (h : SflOddDensityHalf r) :
    Tendsto (fun X : ℕ => (minCount r hr X : ℝ) / X) atTop
      (𝓝 (((r : ℝ) - 1 + √((r : ℝ) ^ 2 - r)) / (4 * r))) := by
  obtain ⟨hJ1, hJ2⟩ := tendsto_J hr
  obtain ⟨hK1, hK2⟩ := tendsto_K hr 0
  simp only [add_zero] at hK1 hK2
  have hF : Tendsto (fun N : ℕ => (oddCount r N : ℝ) / N) atTop (𝓝 (1 / 2)) := h
  have hA := tendsto_comp_ratio hF hJ1 hJ2
  have hB := tendsto_comp_ratio hF hK1 hK2
  have hz : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have := (hz.add hA).sub hB
  rw [zero_add, density_value hr] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  have e := minCount_add_countB hr hX
  rw [countA_eq_oddCount hr, countB_eq_oddCount hr] at e
  have e' : (minCount r hr X : ℝ) = 1 + oddCount r ⌊((X : ℝ) + 1) / betaQ r⌋₊ -
      oddCount r (X / (2 * r)) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) e; push_cast at this; linarith
  rw [e']
  ring

end Count

/-! ## The partner `W_β`: no finite orbit in `ℕ⁺` -/

section Partner

variable {r : ℕ}

/-- Partner entry points: odd `y > 0` with an even preimage (`y = ⌊kβ⌋`) that is not `2rj − 1`
for a `j` with `W'(2j − 1)` even. -/
def IsEntryP (r : ℕ) (y : ℤ) : Prop :=
  0 < y ∧ y % 2 = 1 ∧ (∃ k : ℤ, wqp r (2 * k) = y) ∧
    ∀ j : ℤ, wqp r (2 * j - 1) % 2 = 0 → 2 * r * j - 1 ≠ y

/-- `W'` satisfies the skeleton hypotheses with the odds as the climbing class. -/
lemma wqp_skel (hr : 2 ≤ r) : Skel (wqpPerm r hr) fun y => y % 2 = 1 where
  pos y := wqp_pos_iff hr y
  up y hy he := by
    obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k - 1 := ⟨(y + 1) / 2, by omega⟩
    rw [wqpPerm_apply]
    exact (wqp_bounds hr (show 1 ≤ k by omega)).2.2
  twoStep y hy he hne := by
    obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k - 1 := ⟨(y + 1) / 2, by omega⟩
    simp only [wqpPerm_apply] at hne ⊢
    rw [wqp_wqp_of_even hr k (by omega)]
    have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
    refine ⟨by rw [mul_assoc]; omega, by nlinarith⟩
  down y hy he := by
    obtain ⟨k, rfl⟩ : ∃ k, y = 2 * k := ⟨y / 2, by omega⟩
    rw [wqpPerm_apply]
    exact (wqp_bounds hr (show 1 ≤ k by omega)).2.1.le

/-- `W'` has no positive fixed point. -/
lemma wqp_ne_self (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) : wqpPerm r hr x ≠ x := by
  rw [wqpPerm_apply]
  obtain ⟨k, rfl | rfl⟩ : ∃ k, x = 2 * k ∨ x = 2 * k - 1 := ⟨(x + 1) / 2, by omega⟩
  · exact (wqp_bounds hr (show 1 ≤ k by omega)).2.1.ne
  · exact (wqp_bounds hr (show 1 ≤ k by omega)).2.2.ne'

/-- **(ratified).**  Partner entry points are the positive odd `y` with `W'⁻¹ y`, `W'⁻² y`
even. -/
theorem isEntryP_iff (hr : 2 ≤ r) (y : ℤ) :
    IsEntryP r y ↔ 0 < y ∧ y % 2 = 1 ∧ (wqpPerm r hr).symm y % 2 = 0 ∧
      (wqpPerm r hr).symm ((wqpPerm r hr).symm y) % 2 = 0 := by
  set σ := wqpPerm r hr with hσ
  constructor
  · rintro ⟨h0, h2, ⟨k, hk⟩, hj⟩
    have hs1 : σ.symm y = 2 * k := by rw [Equiv.symm_apply_eq]; exact hk.symm
    refine ⟨h0, h2, by rw [hs1]; omega, ?_⟩
    rw [hs1]
    by_contra hodd
    obtain ⟨j, hj2⟩ : ∃ j, σ.symm (2 * k) = 2 * j - 1 := ⟨(σ.symm (2 * k) + 1) / 2, by omega⟩
    have hwj : wqp r (2 * j - 1) = 2 * k := by
      rw [← wqpPerm_apply hr, ← hj2]; exact σ.apply_symm_apply _
    refine hj j (by rw [hwj]; omega) ?_
    rw [← wqp_wqp_of_even hr j (by rw [hwj]; omega), hwj, hk]
  · rintro ⟨h0, h2, h3, h4⟩
    refine ⟨h0, h2, ⟨σ.symm y / 2, ?_⟩, fun j hj hy => ?_⟩
    · rw [show 2 * (σ.symm y / 2) = σ.symm y by omega, ← wqpPerm_apply hr]
      exact σ.apply_symm_apply y
    · have e1 : σ.symm y = wqp r (2 * j - 1) := by
        rw [Equiv.symm_apply_eq, wqpPerm_apply, wqp_wqp_of_even hr j hj, hy]
      have e2 : σ.symm (σ.symm y) = 2 * j - 1 := by
        rw [e1, Equiv.symm_apply_eq, wqpPerm_apply]
      rw [e2] at h4
      omega

lemma isEntryP_iff_skEntry (hr : 2 ≤ r) (y : ℤ) :
    IsEntryP r y ↔ SkEntry (wqpPerm r hr) (fun y => y % 2 = 1) y := by
  rw [isEntryP_iff hr]
  unfold SkEntry
  constructor <;> rintro ⟨a, b, c, d⟩ <;> exact ⟨a, b, by omega, by omega⟩

/-- **(ratified, partner structure).**  Every orbit through `x > 0` contains exactly one partner
entry point.  Paper proof: Theorem F with parities swapped: odd points of a forward orbit
increase (`W'(2k − 1) > 2k − 1`, or `W'²(2k − 1) = 2rk − 1 > 2k − 1`), even points decrease
(`W'(2k) < 2k`), so an all-even orbit is impossible and there is a first odd point. -/
theorem existsUnique_isEntryP_mem_orbit (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    ∃! e, IsEntryP r e ∧ e ∈ permOrbit (wqpPerm r hr) x := by
  simp_rw [isEntryP_iff_skEntry hr]
  exact (wqp_skel hr).existsUnique_entry hx (wqp_ne_self hr hx)

/-- **(ratified, partner minimum).** -/
theorem isEntryP_lt_of_mem_orbit (hr : 2 ≤ r) {e y : ℤ} (he : IsEntryP r e)
    (hy : y ∈ permOrbit (wqpPerm r hr) e) (hne : y ≠ e) : e < y := by
  exact (wqp_skel hr).entry_lt ((isEntryP_iff_skEntry hr e).1 he) hy hne

/-- **(ratified, partner: no finite orbit in `ℕ⁺`).** -/
theorem permOrbit_wqpPerm_infinite (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    (permOrbit (wqpPerm r hr) x).Infinite := by
  exact (wqp_skel hr).permOrbit_infinite hx (wqp_ne_self hr hx)

/-- **(ratified, partner forward escape).** -/
theorem tendsto_wqpPerm_pow (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (wqpPerm r hr ^ n) x) atTop atTop := by
  exact (wqp_skel hr).tendsto_pow hx (wqp_ne_self hr hx)

/-- **(ratified, partner backward escape).** -/
theorem tendsto_wqpPerm_pow_neg (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (wqpPerm r hr ^ (-(n : ℤ))) x) atTop atTop := by
  exact (wqp_skel hr).tendsto_pow_neg hx (wqp_ne_self hr hx)

/-- **(ratified, partner orbit minima).**  For `x > 0`: `x` is the minimum of its orbit iff `x`
is a partner entry point. -/
theorem isOrbitMinP_iff (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    (∀ y ∈ permOrbit (wqpPerm r hr) x, x ≤ y) ↔ IsEntryP r x := by
  constructor
  · intro hmin
    exact (isEntryP_iff_skEntry hr x).2
      ((wqp_skel hr).entry_of_min hx (wqp_ne_self hr hx) (mem_permOrbit_self x) hmin)
  · intro he y hy
    by_cases h : y = x
    · rw [h]
    · exact (isEntryP_lt_of_mem_orbit hr he hy h).le

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

/-- `A′(X)` counts the odd `y ∈ [1, X]` in the even branch of `W'`. -/
lemma countAP_eq (hr : 2 ≤ r) (X : ℕ) [DecidablePred fun y : ℤ =>
      y % 2 = 1 ∧ ∃ k : ℤ, wqp r (2 * k) = y] :
    countAP r X = ((Finset.Icc (1 : ℤ) X).filter fun y =>
      y % 2 = 1 ∧ ∃ k : ℤ, wqp r (2 * k) = y).card := by
  unfold countAP
  apply Finset.card_nbij (fun k : ℕ => wqp r (2 * (k : ℤ)))
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hk ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hk
    have := (wqp_bounds hr (show (1 : ℤ) ≤ k by exact_mod_cast h1)).1
    exact ⟨⟨by omega, h3⟩, h4, k, rfl⟩
  · intro a _ b _ h
    simp only [wqp_two_mul, ← wq_two_mul_sub_one] at h
    have := (wq_odd_strictMono hr).injective h
    exact_mod_cast this
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hy
    obtain ⟨⟨h1, h2⟩, h3, k, rfl⟩ := hy
    have hk1 : 1 ≤ k := by
      by_contra h
      have := (wqp_pos_iff hr (2 * k)).1 (by omega)
      omega
    have := (wqp_bounds hr hk1).1
    refine ⟨k.toNat, ?_, ?_⟩
    · simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq,
        Int.toNat_of_nonneg (show 0 ≤ k by omega)]
      exact ⟨⟨by omega, by omega⟩, h2, h3⟩
    · simp only [Int.toNat_of_nonneg (show 0 ≤ k by omega)]

/-- `B′(X)` counts the `2rj − 1 ∈ [1, X]` with `W'(2j − 1)` even. -/
lemma countBP_eq (hr : 2 ≤ r) (X : ℕ) [DecidablePred fun y : ℤ =>
      ∃ j : ℤ, wqp r (2 * j - 1) % 2 = 0 ∧ 2 * r * j - 1 = y] :
    countBP r X = ((Finset.Icc (1 : ℤ) X).filter fun y =>
      ∃ j : ℤ, wqp r (2 * j - 1) % 2 = 0 ∧ 2 * r * j - 1 = y).card := by
  unfold countBP
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  apply Finset.card_nbij (fun j : ℕ => 2 * (r : ℤ) * j - 1)
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hj ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hj
    have h1' : (1 : ℤ) ≤ j := by exact_mod_cast h1
    exact ⟨⟨by nlinarith, h3⟩, j, h4, rfl⟩
  · intro a _ b _ h
    have : (a : ℤ) = b := by
      have h' : (2 * (r : ℤ)) * a = (2 * r) * b := by simp only at h; linarith
      exact mul_left_cancel₀ (by omega) h'
    exact_mod_cast this
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hy
    obtain ⟨⟨h1, h2⟩, j, h3, rfl⟩ := hy
    have hj1 : 1 ≤ j := by
      by_contra h
      nlinarith
    have hjX : j ≤ X := by nlinarith
    refine ⟨j.toNat, ?_, ?_⟩
    · simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq,
        Int.toNat_of_nonneg (show 0 ≤ j by omega)]
      exact ⟨⟨by omega, by omega⟩, h2, h3⟩
    · simp only [Int.toNat_of_nonneg (show 0 ≤ j by omega)]

/-- **(ratified, partner exact count).**  `#{orbit minima ≤ X} = A′(X) − B′(X)`. -/
theorem minCountP_add_countBP (hr : 2 ≤ r) (X : ℕ) :
    minCountP r hr X + countBP r X = countAP r X := by
  classical
  set S := Finset.Icc (1 : ℤ) X with hS
  rw [countAP_eq hr X, countBP_eq hr X]
  have hBA : ∀ y, (∃ j : ℤ, wqp r (2 * j - 1) % 2 = 0 ∧ 2 * r * j - 1 = y) →
      y % 2 = 1 ∧ ∃ k : ℤ, wqp r (2 * k) = y := by
    rintro y ⟨j, hj, rfl⟩
    refine ⟨by rw [mul_assoc]; omega, wqp r (2 * j - 1) / 2, ?_⟩
    rw [show 2 * (wqp r (2 * j - 1) / 2) = wqp r (2 * j - 1) by omega,
      wqp_wqp_of_even hr j hj]
  have hsplitA := Finset.card_filter_add_card_filter_not
    (s := S.filter fun y => y % 2 = 1 ∧ ∃ k : ℤ, wqp r (2 * k) = y)
    (fun y => ∃ j : ℤ, wqp r (2 * j - 1) % 2 = 0 ∧ 2 * r * j - 1 = y)
  have e1 : ((S.filter fun y => y % 2 = 1 ∧ ∃ k : ℤ, wqp r (2 * k) = y).filter
      fun y => ∃ j : ℤ, wqp r (2 * j - 1) % 2 = 0 ∧ 2 * r * j - 1 = y) =
      S.filter fun y => ∃ j : ℤ, wqp r (2 * j - 1) % 2 = 0 ∧ 2 * r * j - 1 = y := by
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, hBA y h3⟩, h3⟩
  have e3 : (S.filter fun x => ∀ y ∈ permOrbit (wqpPerm r hr) x, x ≤ y) =
      ((S.filter fun y => y % 2 = 1 ∧ ∃ k : ℤ, wqp r (2 * k) = y).filter
      fun y => ¬∃ j : ℤ, wqp r (2 * j - 1) % 2 = 0 ∧ 2 * r * j - 1 = y) := by
    ext y
    simp only [Finset.mem_filter, hS, Finset.mem_Icc]
    constructor
    · rintro ⟨hy, hmin⟩
      obtain ⟨-, h2, h3, h4⟩ := (isOrbitMinP_iff hr (by omega)).1 hmin
      exact ⟨⟨hy, h2, h3⟩, fun ⟨j, hj, hjy⟩ => h4 j hj hjy⟩
    · rintro ⟨⟨hy, h2, h3⟩, h4⟩
      exact ⟨hy, (isOrbitMinP_iff hr (by omega)).2
        ⟨by omega, h2, h3, fun j hj hjy => h4 ⟨j, hj, hjy⟩⟩⟩
  unfold minCountP
  rw [← hsplitA, e1, e3]
  ring

/-- `#{k ∈ [1, N] : sfl r k even}`. -/
def evenCount (r N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun k : ℕ => sfl r k % 2 = 0).card

lemma evenCount_add_oddCount (r N : ℕ) : evenCount r N + oddCount r N = N := by
  unfold evenCount oddCount
  have := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 N)
    (fun k : ℕ => sfl r k % 2 = 0)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  have e : ((Finset.Icc 1 N).filter fun k : ℕ => ¬sfl r k % 2 = 0) =
      (Finset.Icc 1 N).filter fun k : ℕ => sfl r k % 2 = 1 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [e] at this
  exact this

lemma countAP_eq_evenCount (hr : 2 ≤ r) (X : ℕ) :
    countAP r X = evenCount r ⌊((X : ℝ) + 1) / betaQ r⌋₊ := by
  unfold countAP evenCount
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, le_floor_iff_wq hr]
  have hw : wqp r (2 * k) = wq r (2 * k - 1) := by rw [wqp_two_mul, wq_two_mul_sub_one]
  have hpar : wqp r (2 * k) % 2 = 1 ↔ sfl r k % 2 = 0 := by
    rw [wqp_two_mul, show (2 : ℤ) * r * k = 2 * (r * k) by ring]; omega
  rw [hpar, hw]
  constructor
  · rintro ⟨⟨h1, -⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h4⟩
  · rintro ⟨⟨h1, h3⟩, h4⟩
    have := (wq_two_mul_sub_one_bounds hr (show (1 : ℤ) ≤ k by exact_mod_cast h1)).1
    exact ⟨⟨h1, by omega⟩, h3, h4⟩

lemma countBP_eq_evenCount (hr : 2 ≤ r) (X : ℕ) :
    countBP r X = evenCount r ((X + 1) / (2 * r)) := by
  unfold countBP evenCount
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  have hpar : wqp r (2 * j - 1) % 2 = 0 ↔ sfl r j % 2 = 0 := by
    rw [wqp_two_mul_sub_one, show (2 : ℤ) * r * j = 2 * (r * j) by ring]; omega
  have hle : 2 * (r : ℤ) * j - 1 ≤ X ↔ j * (2 * r) ≤ X + 1 := by
    constructor
    · intro h; have : ((j * (2 * r) : ℕ) : ℤ) ≤ ((X + 1 : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · intro h; have : ((j * (2 * r) : ℕ) : ℤ) ≤ ((X + 1 : ℕ) : ℤ) := by exact_mod_cast h
      push_cast at this; linarith
  rw [hpar, hle, Nat.le_div_iff_mul_le (by omega)]
  constructor
  · rintro ⟨⟨h1, -⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h4⟩
  · rintro ⟨⟨h1, h3⟩, h4⟩
    exact ⟨⟨h1, by nlinarith⟩, h3, h4⟩

/-- There are `⌊(X + 1)/2⌋` odd integers in `[1, X]`. -/
lemma card_filter_odd (X : ℕ) :
    ((Finset.Icc (1 : ℤ) X).filter fun y => y % 2 = 1).card = (X + 1) / 2 := by
  rw [show (X + 1) / 2 = (Finset.Icc 1 ((X + 1) / 2)).card by simp]
  symm
  apply Finset.card_nbij (fun j : ℕ => 2 * (j : ℤ) - 1)
  · intro j hj
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.coe_filter, Finset.mem_Icc,
      Set.mem_ofPred_eq] at hj ⊢
    omega
  · intro a _ b _ h
    have : (a : ℤ) = b := by simp only at h; omega
    exact_mod_cast this
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hy
    refine ⟨((y + 1) / 2).toNat, ?_, ?_⟩
    · simp only [Finset.coe_Icc, Set.mem_Icc]; omega
    · simp only; omega

/-- `A′(X) ≥ ⌊(X + 1)/2⌋ − ⌊X/(4r − 2)⌋`. -/
lemma countAP_ge (hr : 2 ≤ r) (X : ℕ) : (X + 1) / 2 ≤ countAP r X + X / (4 * r - 2) := by
  classical
  rw [countAP_eq hr X, ← card_filter_odd X]
  refine (Finset.card_le_card ?_).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (card_even_branch_le hr X) _))
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_union] at hy ⊢
  obtain ⟨n, hn⟩ := (wqp_bijective hr).2 y
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k - 1 := ⟨(n + 1) / 2, by omega⟩
  · exact Or.inl ⟨hy.1, hy.2, k, hn⟩
  · refine Or.inr ⟨hy.1, k, ?_⟩
    rw [← hn, wqp_two_mul_sub_one, wq_two_mul]

/-- `B′(X) ≤ ⌊(X + 1)/2r⌋`. -/
lemma countBP_le (hr : 2 ≤ r) (X : ℕ) : countBP r X ≤ (X + 1) / (2 * r) := by
  unfold countBP
  calc _ ≤ (Finset.Icc 1 ((X + 1) / (2 * r))).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
          refine ⟨hj.1.1, (Nat.le_div_iff_mul_le (by omega)).2 ?_⟩
          have h := hj.2.1
          have : ((j * (2 * r) : ℕ) : ℤ) ≤ ((X + 1 : ℕ) : ℤ) := by push_cast; linarith
          exact_mod_cast this
    _ = (X + 1) / (2 * r) := by simp

/-- **(ratified, partner conclusion).** -/
theorem wqpPerm_infinitelyManyInfiniteOrbits (hr : 2 ≤ r) :
    InfinitelyManyInfiniteOrbits (wqpPerm r hr) := by
  have hE : {y | IsEntryP r y}.Infinite := by
    intro hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    set N := B.toNat + 2 with hN
    have hle : minCountP r hr (12 * N) ≤ B.toNat := by
      classical
      unfold minCountP
      calc _ ≤ (Finset.Icc (1 : ℤ) B.toNat).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
              obtain ⟨⟨h1, h2⟩, h3⟩ := hx
              have := hB ((isOrbitMinP_iff hr (by omega)).1 h3)
              omega
        _ = B.toNat := by simp; omega
    have e := minCountP_add_countBP hr (12 * N)
    have hA := countAP_ge hr (12 * N)
    have hB' := countBP_le hr (12 * N)
    have d1 : 12 * N / (4 * r - 2) ≤ 12 * N / 6 := Nat.div_le_div_left (by omega) (by norm_num)
    have d2 : (12 * N + 1) / (2 * r) ≤ (12 * N + 1) / 4 :=
      Nat.div_le_div_left (by omega) (by norm_num)
    omega
  have hinj : Set.InjOn (permOrbit (wqpPerm r hr)) {y | IsEntryP r y} := by
    intro a ha b hb hab
    have h1 := (isOrbitMinP_iff hr ha.1).2 ha b (by rw [hab]; exact mem_permOrbit_self b)
    have h2 := (isOrbitMinP_iff hr hb.1).2 hb a (by rw [← hab]; exact mem_permOrbit_self a)
    exact le_antisymm h1 h2
  refine (hE.image hinj).mono ?_
  rintro _ ⟨e, he, rfl⟩
  exact ⟨e, he.1.le, rfl, permOrbit_wqpPerm_infinite hr he.1⟩

/-- **(ratified, partner density, conditional on equidistribution).**  Same `d_r`:
`⌊kβ⌋ = 2rk − sfl − 1` is odd iff `sfl r k` is even. -/
theorem tendsto_minCountP (hr : 2 ≤ r) (h : SflOddDensityHalf r) :
    Tendsto (fun X : ℕ => (minCountP r hr X : ℝ) / X) atTop
      (𝓝 (((r : ℝ) - 1 + √((r : ℝ) ^ 2 - r)) / (4 * r))) := by
  obtain ⟨hJ1, hJ2⟩ := tendsto_J hr
  obtain ⟨hK1, hK2⟩ := tendsto_K hr 1
  have hF : Tendsto (fun N : ℕ => (oddCount r N : ℝ) / N) atTop (𝓝 (1 / 2)) := h
  have hG : Tendsto (fun N : ℕ => (evenCount r N : ℝ) / N) atTop (𝓝 (1 / 2)) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hF
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (N : ℝ) ≠ 0 := by positivity
    have e := evenCount_add_oddCount r N
    have e' : (evenCount r N : ℝ) = N - oddCount r N := by
      have := congrArg (fun n : ℕ => (n : ℝ)) e; push_cast at this; linarith
    rw [e']
    field_simp
  have hA := tendsto_comp_ratio hG hJ1 hJ2
  have hB := tendsto_comp_ratio hG hK1 hK2
  have := hA.sub hB
  rw [density_value hr] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  have e := minCountP_add_countBP hr X
  rw [countAP_eq_evenCount hr, countBP_eq_evenCount hr] at e
  have e' : (minCountP r hr X : ℝ) = evenCount r ⌊((X : ℝ) + 1) / betaQ r⌋₊ -
      evenCount r ((X + 1) / (2 * r)) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) e; push_cast at this; linarith
  rw [e']
  ring

end Partner

end CollatzMoonshot.WythoffQuadratic
