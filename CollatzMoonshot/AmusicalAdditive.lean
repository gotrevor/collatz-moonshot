/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalTwin

/-!
# The additive side: twins are translates, and the carry is unbounded

The 2026-10-14 "ringadd" agent tested the additive structure of `ℤ` against Klamkin (a).

**Theorem T (agent; research §27).**  Every twin `W_{α,β,γ}` (`W(2m) = 3m+α`, `W(4m+1) = 3m+β`,
`W(4m+3) = 3m+γ`) is a layer map `U_q` plus the constant `d = (α+β+γ−3)/3`, after a unique even
translation, with `q = 3 − 2(γ − β)`.  The agent checked all 6600 twins with offsets of size at most
`15`.  So the statistical twins are `Û + c` on the lattices `(1/q)ℤ`, not new maps, and Kohl's
determinant of a twin is `d`.

**`twinW_eq_translate`.**  The case `q = 1`, `d = 1`: `twinW x = U(x + 4) − 3`, i.e. `twinW` is
`U + 1` conjugated by translation by `4`.

**`amusical_carry_unbounded`.**  The additive carry `U(x+y) − U x − U y` is unbounded
(`x = y = 4k + 1` gives `6k + 1`).  So no finite-valued additive cocycle transports orbits.  The
agent also refuted a Baker-type contrapositive: the relations between `log 2` and `log 3` that
finitely many orbits would force are only Dirichlet-sized, which every irrational satisfies.
-/

namespace CollatzMoonshot.Amusical

/-- **Proved.**  `twinW` is `U + 1` conjugated by the translation `x ↦ x + 4`. -/
theorem twinW_eq_translate (x : ℤ) : twinW x = amusical (x + 4) - 3 := by
  unfold twinW amusical
  split_ifs <;> omega

/-- **Proved.**  The carry `U(x + y) − U x − U y` is unbounded above. -/
theorem amusical_carry_unbounded (B : ℤ) :
    ∃ x y : ℤ, B < amusical (x + y) - amusical x - amusical y := by
  refine ⟨4 * |B| + 1, 4 * |B| + 1, ?_⟩
  unfold amusical
  have := abs_nonneg B
  have := le_abs_self B
  split_ifs <;> omega

end CollatzMoonshot.Amusical
