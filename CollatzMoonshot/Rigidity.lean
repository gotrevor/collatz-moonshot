/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Rigidity.Padic
import CollatzMoonshot.Rigidity.Drift
import CollatzMoonshot.Rigidity.Funnel
import CollatzMoonshot.Rigidity.Circle
import CollatzMoonshot.Rigidity.Furstenberg
import CollatzMoonshot.Rigidity.Invariant
import CollatzMoonshot.Rigidity.Empirical

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
* `Furstenberg.isClosed_invariant_finite_or_univ` (`Furstenberg.lean`) -
  **Furstenberg's 1967 topological ×p×q rigidity, PROVED axiom-clean**
  (2026-08-26, Boshernitzan's elementary route via Manners arXiv:1305.1514 §4),
  with the density corollary `dense_orbit_of_not_isOfFinAddOrder`.  The former
  THEOREM-grade axiom in `Assumed/Furstenberg.lean` is discharged: same name,
  same statement, now a theorem.
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
  functional; blocker: KS entropy missing from mathlib.  (Its topological
  sibling, formerly the `furstenberg_topological_rigidity` axiom, is now a
  proved theorem - see above.)

## Milestones
* **M1** (done): vocabulary + base intertwining + funnel + wiring forms.
* **M2′** (done): `ParityRigidityW1' → NoDivergentOrbit`, proved in
  `Rigidity/Empirical.lean`.  The theorem includes Krylov-Bogolyubov transfer on
  compact `ℤ_[2]`, orbit-closure support, clopen Portmanteau, a uniform sub-sharp
  empirical `limsup`, and high-tail drift consumption.  It is sorry-free and its
  axiom footprint is the trust base only.
  `FrontA/Threads.lean` additionally pins the weaker empirical-limit version and
  the expected calibration `ParityRigidityW1' ↔ NoDivergentOrbit`, so proving
  the completed measure plumbing cannot be mistaken for proving the rigidity input itself.
* **M2** (superseded, kept as the alternate route): `MeasureRigidityW1 →
  NoDivergentOrbit` via the frequency/all-scales upgrade of the funnel.  Harder:
  deep 2-adic returns are rare enough that the counting does not obviously close.
* **M3**: the intertwining conjecture proper - relate `T2`-invariant orbit-limit
  measures to the ×2,×3 structure the circle model rigidifies (transfer
  principles of the 2⊥3 trinity).
* **M4**: KS entropy lands in mathlib → instantiate Rudolph-Johnson, retire the
  parameter.
-/
