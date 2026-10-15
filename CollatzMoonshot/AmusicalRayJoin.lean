/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalGlobal

/-!
# Ray joins: the orbit of `3^m` cannot reach a power of 2 early (research §52)

The *ray* `2^m → 3·2^{m−1} → ⋯ → 3^m` is the maximal run of `S`-units (`S = {2, 3}`) on an orbit: an
orbit enters it only at `2^m` and leaves only at `3^m`.  A *join* is `U^k(3^m) = 2^{m′}`; it is the
`S`-unit equation `2^{b_k + m′} − 3^{k+m} = C_k` for the prefix word of length `k`.  Round-5
ideation (2026-10-15, Fable, "Theorem J") combined the exact error bound along the orbit with
Ellison's explicit lower bound for `|2^x − 3^y|` to show a ray cannot join within about
`2.1m` steps, past the residue horizon `≈ 1.06m`.  Ellison's theorem enters as the hypothesis
`EllisonBound`.

* `ray_join_three`, `ray_join_four`: the two known joins, `27 → 32` in 9 steps and `81 → 512` in 37.
* `no_early_ray_join`: given `EllisonBound`, `U^k(3^m)` is not a power of 2 for `1 ≤ k ≤ 2m − 2`.

Conjecture J (research §52, 60%): joins happen only from `3^1, …, 3^4`; it would imply (a).
-/

namespace CollatzMoonshot.Amusical

/-- **Literature (Ellison, Séminaire de Théorie des Nombres de Bordeaux 1970/71, exp. 12, Thm 3).**
`|2^x − 3^y| > 2^x e^{−x/10}` for positive `x, y` with `x` outside an explicit finite set. -/
def EllisonBound : Prop :=
  ∀ x y : ℕ, 0 < x → 0 < y →
    x ∉ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 19, 27} : Finset ℕ) →
    (2 : ℝ) ^ x * Real.exp (-(x : ℝ) / 10) < |(2 : ℝ) ^ x - 3 ^ y|

/-- **Target.**  The ray of `27` joins `32` after 9 steps. -/
theorem ray_join_three : amusical^[9] 27 = 32 := by
  sorry

/-- **Target.**  The ray of `81` joins `512` after 37 steps. -/
theorem ray_join_four : amusical^[37] 81 = 512 := by
  sorry

/-- **Target (Theorem J).**  Given Ellison's bound, the orbit of `3^m` meets no power of 2 within
its first `2m − 2` steps. -/
theorem no_early_ray_join (hE : EllisonBound) (m k m' : ℕ) (hk : 1 ≤ k) (hkm : k + 2 ≤ 2 * m) :
    amusical^[k] ((3 : ℤ) ^ m) ≠ 2 ^ m' := by
  sorry

end CollatzMoonshot.Amusical
