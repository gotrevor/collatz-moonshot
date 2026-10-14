/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalCrossing

/-!
# The deformation `U + c` and its degenerate point `c = 0`

Klamkin (a) is the `c = 0` point of the family `Û + c`, and every rational `c ≠ 0` has
infinitely many infinite orbits on `ℚ ∩ ℤ_(6)` (research §27, T5).  The 2026-10-14 "deform" agent
asked whether anything carries over to `c = 0`.  It does not, and the reason is inside the family.

**`amusical_add_roots_distinct`.**  For an integer `d > 0`, the forward orbit of any `y ≥ 0` under
`U + d` stays at or above `d` after one step, since `U` preserves sign.  So the points
`0, 1, …, d − 1` lie on `d` pairwise distinct infinite orbits of `U + d` (the agent's Prop R: they
are exactly the landing points of the `d` up-crossings).

Take `d = 6^N → 0` in `ℤ₂ × ℤ₃`.  The itineraries of `U + d` agree with `U`'s for about `N/1.5`
steps forward and `N` back, yet every point of `[0, 6^N)`, including `U`'s 5-cycle, is on its own
infinite orbit.  Orbit structure has no limit at the degenerate point.  Small denominators fuse
orbits instead (at `c = 1/5` the 5-cycle joins `0, 1, 2, 3, 8`).  The flux of `U_Q + k` on every
periodic invariant piece is `k` times its density, linear in `c` with no mode locking (agent's
Theorem Z).

Paper proofs: agent report `deform.md`, summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §29.
-/

namespace CollatzMoonshot.Amusical

/-- **Proved.**  After one step of `U + d` (`d ≥ 0`), a nonnegative point is at least `d`. -/
theorem amusical_add_iterate_ge {d : ℤ} (hd : 0 ≤ d) {y : ℤ} (hy : 0 ≤ y) (t : ℕ) :
    d ≤ (fun x => amusical x + d)^[t + 1] y := by
  induction t with
  | zero => simpa using amusical_nonneg hy
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      have := amusical_nonneg (show 0 ≤ (fun x => amusical x + d)^[t + 1] y by omega)
      omega

/-- **Proved.**  The points `0, …, d − 1` lie on pairwise distinct infinite orbits of `U + d`: no
point of `[0, d)` is a forward iterate (of length `≥ 1`) of another, or of itself. -/
theorem amusical_add_roots_distinct {d j j' : ℤ} (hd : 0 ≤ d) (hj : 0 ≤ j) (hj' : j' < d)
    (t : ℕ) : (fun x => amusical x + d)^[t + 1] j ≠ j' := by
  have := amusical_add_iterate_ge hd hj t
  omega

end CollatzMoonshot.Amusical
