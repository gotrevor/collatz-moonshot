/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.FourierPair

/-!
# No long runs: the Diophantine input that would close `PairBoundDecay`

The direct port of Tao's Prop 7.3 to the pairing walk fails (research note §12): the mirror walk
is shallower than its black triangles, so one triangle can trap it for the rest of its length (the
resonance does exactly that).  The protection lemma `pairTheta_far` caps traps whose corner sits
near the walk, but not traps whose corner sits far above it.  This module records the pointwise
input that would cap every trap at `O(log n)` pairs.

* **The node** (`NoLongRuns`): for fixed odd `ξ`, `Θ(k, t) = ⟨ξ·3^{−t}⟩_k` stays at distance
  `≥ (k + t)^{−C}` from the integers.  Equivalently the 2-adic numbers `ξ·3^{−t}` have no binary
  run longer than `C log₂(k + t)` ending at bit `k`.  For `ξ = 1`, `Θ(k, t)` is
  `(2^{−k} mod 3^t)/3^t` up to `1/(3^t 2^k)`, so the same statement reads: the 3-adic digits of
  `2^{−k}` have no run of `0`s or `2`s longer than `C log₃(k + t)` ending at position `t`.  Both
  are the near-coincidence `|2^k a − 3^t b|` small, in the neighbourhood of Erdős's
  ternary-digits-of-`2^n` problem.
* **Evidence** (`experiments/conjugacy/runs.py`, `traps.py`, field `k ≤ 4000`, `t ≤ 2000`):
  the empirical exponent `max log(1/‖Θ‖)/log(k + t)` is `2.09, 2.28, 1.95, 2.00` at
  `ξ = 1, 5, 7, 11` over the whole field and `1.94, 1.90, 1.95, 1.87` over `k + t ≥ 1000`,
  i.e. at the critical value `2` of a random-field model, where Borel–Cantelli predicts finitely
  many violations for every `C > 2`; it does not creep upward.  Along walk lines the longest
  trap is `8–9` pairs (of up to `2000`) for `ξ = 1, 5, 7`, against `1000` for the control
  `ξ = 3^{1000}`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology

/-- **Node: no long runs.**  For each odd `ξ` there are `C` and `K₀` with
`(k + t)^{−C} ≤ |Θ(k, t) − z|` for every integer `z`, every `k ≥ K₀` and every `t` with
`3^t ∤ ξ` (the finitely many columns `t ≤ v₃(ξ)` are the resonant ones and are excluded).
Confidence 75% (random-field heuristic and the measurements above; pointwise, so a single
exceptional near-coincidence would refute it). -/
def NoLongRuns : Prop :=
  ∀ ξ : ℕ, Odd ξ → ∃ C K₀ : ℕ, ∀ k t : ℕ, K₀ ≤ k → ¬ 3 ^ t ∣ ξ → ∀ z : ℤ,
    ((k + t : ℕ) : ℝ) ^ (-(C : ℝ)) ≤ |pairTheta ξ k t - z|

/-- **Edge (the frontier one): no long runs implies the positive walk decays.**  Sketch: under
`NoLongRuns`, every black triangle the walk can meet has size `≤ C log n + O(1)`, so the walk
leaves each within `O(log n)` pairs; the mirrored Lemma 7.4 (black set a union of triangles
separated by `≫ log(1/ε)`, metric `(log 4, log 3)`) puts white points around each exit, and the
walk lands on one at a single-step pair with probability `≫ 1`; so `≫ n / log n` white factors
are collected with high probability and `U_n ≤ exp(−c ε³ n / log n) + o(1)`.  Not routine: it is
Tao §7.2–7.4 rebuilt for the mirror walk with the budget (7.52) replaced by the run bound.
Confidence 55%. -/
theorem pairBoundDecay_of_noLongRuns (h : NoLongRuns) : PairBoundDecay := by
  sorry

end CollatzMoonshot.Conjugacy
