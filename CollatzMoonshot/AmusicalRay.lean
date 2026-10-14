/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalPowers

/-!
# Forward survivors on a ray: the powers of `2`

The 2026-10-14 "rayfs" agent asked whether one explicit ray holds infinitely many forward
survivors (research §34).  No ray is settled, but the question reduces to the powers of `2`.

**`not_fwdSurvivor_of_odd`.**  Odd `y > 1` has `U y < y`, so an odd ray (`5ᵏ`, …) holds no
forward survivor past its first member.

**`threeSmooth_fwdSurvivor_infinite_iff`.**  On a staircase `2^(s−b) 3^b y` the forward survivors
form an initial segment (`staircase_fwdSurvivor_iff`), so infinitely many `3`-smooth forward
survivors is the same as infinitely many forward survivors among the `2ˢ` (Ray(2)).

**`pow_two_drop_bound` (Theorem DE).**  `U y + 1 ≥ ¾ (y + 1)` on every branch, so after the climb
`2ˢ m ↦ 3ˢ m` the orbit needs `t > s · log(3/2)/log(4/3) ≈ 1.41 s` further steps to return below
`2ˢ m`.  It must consume every binary digit of `3ˢ m` first: Ray(2) is a pure late-drop question.

**`infinitelyManyOrbits_of_pow_two_orbitMin` (M2).**  Infinitely many powers of `2` that are orbit
minima give Klamkin (a).  Measured backward-survivor rate of `2ˢ`: `0.3576` (predicted `0.3553`).

**`ConjP2`.**  Every `2ˢ` is a forward survivor (BELIEVED 90%; `s ≤ 3000` pass a walk proxy, and
the Haar model expects `0.78` failures).  A single `Π⁰₁` sentence that implies Ray(2).
-/

namespace CollatzMoonshot.Amusical

/-- **Target.**  `U` lowers every odd number above `1`. -/
theorem amusical_lt_of_odd {y : ℤ} (h1 : 1 < y) (h : Odd y) : amusical y < y := by
  sorry

/-- **Target.**  An odd number above `1` is not a forward survivor. -/
theorem not_fwdSurvivor_of_odd {y : ℤ} (h1 : 1 < y) (h : Odd y) : ¬ FwdSurvivor y := by
  sorry

/-- **Target (Lemma IS).**  A staircase point below the top survives iff it lies at or below the
top's forward orbit. -/
theorem staircase_fwdSurvivor_iff {y : ℤ} (hy : 0 < y) {s b : ℕ} (hb : b < s) :
    FwdSurvivor (2 ^ (s - b) * 3 ^ b * y) ↔
      ∀ t : ℕ, 2 ^ (s - b) * 3 ^ b * y ≤ amusical^[t] (3 ^ s * y) := by
  sorry

/-- **Target (Corollary H).**  Infinitely many `3`-smooth forward survivors iff infinitely many
powers of `2` are forward survivors. -/
theorem threeSmooth_fwdSurvivor_infinite_iff :
    {n : ℕ | (∃ a b : ℕ, n = 2 ^ a * 3 ^ b) ∧ FwdSurvivor (n : ℤ)}.Infinite ↔
      {s : ℕ | FwdSurvivor ((2 : ℤ) ^ s)}.Infinite := by
  sorry

/-- **Target.**  Each step of `U` on `y ≥ 0` keeps `U y + 1 ≥ ¾ (y + 1)`. -/
theorem amusical_iterate_add_one_ge (t : ℕ) {y : ℤ} (hy : 0 ≤ y) :
    3 ^ t * (y + 1) ≤ 4 ^ t * (amusical^[t] y + 1) := by
  sorry

/-- **Target (Theorem DE).**  After the climb `2ˢ m ↦ 3ˢ m`, `t` more steps lose at most a factor
`(4/3)^t`. -/
theorem pow_two_drop_bound (s t : ℕ) {m : ℤ} (hm : 0 ≤ m) :
    3 ^ t * (3 ^ s * m + 1) ≤ 4 ^ t * (amusical^[s + t] (2 ^ s * m) + 1) := by
  sorry

/-- **Target (M2).**  Infinitely many powers of `2` that are orbit minima imply Klamkin (a). -/
theorem infinitelyManyOrbits_of_pow_two_orbitMin
    (h : {s : ℕ | IsOrbitMin ((2 : ℤ) ^ s)}.Infinite) : AmusicalInfinitelyManyOrbits := by
  sorry

/-- **Open (Conjecture P2, BELIEVED 90%).**  Every power of `2` is a forward survivor. -/
def ConjP2 : Prop :=
  ∀ s t : ℕ, (2 : ℤ) ^ s ≤ amusical^[t] (2 ^ s)

/-- **Target.**  Conjecture P2 gives Ray(2). -/
theorem ray_two_of_conjP2 (h : ConjP2) : {s : ℕ | FwdSurvivor ((2 : ℤ) ^ s)}.Infinite := by
  sorry

end CollatzMoonshot.Amusical
