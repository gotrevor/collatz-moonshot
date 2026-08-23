/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Rigidity.Padic
import CollatzMoonshot.Rigidity.Drift
import CollatzMoonshot.Rigidity.Funnel
import CollatzMoonshot.Rigidity.Circle
import CollatzMoonshot.Rigidity.Invariant

/-!
# Lane 1: ×2×3 measure rigidity 🏔️

The most-likely lane from `APPROACHES.md` (Approach 1, ~40% conditional).  What
lives where, and the roadmap.

## Proved
* `T2_natCast` (`Padic.lean`) - the base intertwining: ℕ-dynamics = ℤ₂-dynamics
  restricted along the embedding.
* `continuous_T2`, `measurable_T2` (`Padic.lean`, `Invariant.lean`) - the parity
  partition is the unit ball, hence clopen; halving is 2-Lipschitz.  This is the
  Krylov-Bogolyubov prerequisite AND the reason parity mass survives a weak-*
  limit.
* `iterate_mul_two_pow_le`, `lt_of_oddSteps_freq_lt`, `tendsto_freqThreshold`
  (`Drift.lean`) - the archimedean bookkeeping: odd-step frequency below
  `log 2 / log (2 · growth N)` forces descent, and that threshold rises to the
  sharp `log 2 / log 6` as the orbit's floor rises.
* `T2_neg_cycle` (`Padic.lean`) - the `-1 → -2` invariant 2-cycle with odd
  frequency `1/2`: the proved witness that unconditioned parity rigidity is
  false.
* `funnel` / `funnel_crash` (`Funnel.lean`) - 2-adic proximity to `1` is an
  archimedean `(3/4)^s` crash: the concrete mechanism giving W1 teeth.
* `conjecture_of_fronts`, `conjecture_iff_descent` (`../Descent.lean`) - the
  consumption forms: Front A + Front B ⟹ Collatz, and descent alone ⟹ Collatz.
* `diverges_iterate_iff`, `noDivergent_of_descends_if_diverges`,
  `noDivergent_of_freq_descent_if_diverges` (`Drift.lean`) - the correctly scoped
  Front-A consumption forms: only starts already assumed divergent must descend;
  hypothetical bounded cycles remain Front B's responsibility.

## Pinned
* **W1′** (`Invariant.lean`) - invariant measures on a positive orbit's 2-adic
  closure give the odd set mass below `log 2 / log 6`.  **The working keystone**
  as of 2026-08-20: it is the quantity that controls archimedean size, so it
  cashes out through `Drift.lean` with no funnel upgrade owed.
* **W1** (`Invariant.lean`) - invariant measures on a positive orbit's 2-adic
  closure charge the trivial cycle.  Retained, not retired: it carries the funnel
  mechanism and M3 may want it.  Strength audit: W1 already excludes every
  positive nontrivial atomic cycle, so unlike W1′ it is not a Front-A-only pin.
  Both are PROGRAM-grade, `def`s by doctrine.
* `RudolphJohnsonStatement` (`Circle.lean`) - parameterized by an entropy
  functional; blocker: KS entropy missing from mathlib.
* `furstenberg_topological_rigidity` (`../Assumed/Furstenberg.lean`) - the
  THEOREM-grade axiom anchoring the circle model.

## Milestones
* **M1** (done): vocabulary + base intertwining + funnel + wiring forms.
* **M2′** (live): `ParityRigidityW1' → NoDivergentOrbit`.  Ingredients:
  (a) `continuous_T2` ✅; (b) Krylov-Bogolyubov transfer on the compact space
  `ℤ_[2]` - THEOREM-grade axiom, quantified over the orbit closure; (c) empirical
  measures + Portmanteau on the clopen parity set, turning `μ oddSetZ2` into the
  limiting odd-step frequency; (d) `lt_of_oddSteps_freq_lt` ✅ to convert that
  frequency into descent, with the floor `N` supplied by the divergence itself.
  Only (b) and (c) remain.
  `FrontA/Threads.lean` additionally pins the weaker empirical-limit version and
  the expected calibration `ParityRigidityW1' ↔ NoDivergentOrbit`, so proving
  measure plumbing cannot be mistaken for proving the rigidity input itself.
* **M2** (superseded, kept as the alternate route): `MeasureRigidityW1 →
  NoDivergentOrbit` via the frequency/all-scales upgrade of the funnel.  Harder:
  deep 2-adic returns are rare enough that the counting does not obviously close.
* **M3**: the intertwining conjecture proper - relate `T2`-invariant orbit-limit
  measures to the ×2,×3 structure the circle model rigidifies (transfer
  principles of the 2⊥3 trinity).
* **M4**: KS entropy lands in mathlib → instantiate Rudolph-Johnson, retire the
  parameter.
-/
