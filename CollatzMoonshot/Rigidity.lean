/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Rigidity.Padic
import CollatzMoonshot.Rigidity.Funnel
import CollatzMoonshot.Rigidity.Circle
import CollatzMoonshot.Rigidity.Invariant

/-!
# Lane 1: ×2×3 measure rigidity 🏔️

The most-likely lane from `APPROACHES.md` (Approach 1, ~40% conditional).  What
lives where, and the roadmap.

## Proved today
* `T2_natCast` (`Padic.lean`) - the base intertwining: ℕ-dynamics = ℤ₂-dynamics
  restricted along the embedding.
* `funnel` / `funnel_crash` (`Funnel.lean`) - 2-adic proximity to `1` is an
  archimedean `(3/4)^s` crash: the concrete mechanism giving W1 teeth.
* `conjecture_of_fronts`, `conjecture_iff_descent` (`../Descent.lean`) - the
  consumption forms: Front A + Front B ⟹ Collatz, and descent alone ⟹ Collatz.

## Pinned
* **W1** (`Invariant.lean`) - invariant measures on a positive orbit's 2-adic
  closure charge the trivial cycle.  PROGRAM-grade, a `def` by doctrine.
* `RudolphJohnsonStatement` (`Circle.lean`) - parameterized by an entropy
  functional; blocker: KS entropy missing from mathlib.
* `furstenberg_topological_rigidity` (`../Assumed/Furstenberg.lean`) - the
  THEOREM-grade axiom anchoring the circle model.

## Milestones
* **M1** (done): vocabulary + base intertwining + funnel + wiring forms.
* **M2**: `MeasureRigidityW1 → NoDivergentOrbit`.  Ingredients: Krylov-Bogolyubov
  transfer on the compact space `ℤ_[2]` (THEOREM-grade axiom when needed:
  continuity of `T2`, existence of invariant limit measures on the orbit
  closure), plus the frequency/all-scales upgrade of the funnel.
* **M3**: the intertwining conjecture proper - relate `T2`-invariant orbit-limit
  measures to the ×2,×3 structure the circle model rigidifies (transfer
  principles of the 2⊥3 trinity).
* **M4**: KS entropy lands in mathlib → instantiate Rudolph-Johnson, retire the
  parameter.
-/
