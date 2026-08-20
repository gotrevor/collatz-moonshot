/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.Rigidity.Padic
import CollatzMoonshot.Rigidity.Drift

/-!
# Invariant measures on ℤ₂ and the pinned working conjecture W1

Borel structure on `ℤ_[2]` (compact metric, so this is the standard setup),
`T2`-invariance via `MeasurePreserving`, and the lane keystone **W1**.

## Why the conditioning in W1 matters

`T2` on `ℤ_[2]` is conjugate to the full one-sided shift (Bernstein-Lagarias), so
its invariant measures form a huge simplex - Bernoulli, Markov, everything.  Any
unconditioned dichotomy over all invariant measures is FALSE.  The rigidity must
come from the *arithmetic* conditioning: W1 quantifies only over invariant
measures supported on the 2-adic closure of an actual positive orbit.  That
support condition is the formal shadow of "arises from ℕ" - the place where the
archimedean structure enters, and exactly the intertwining gap named in
`APPROACHES.md` (Approach 1, "the new math").
-/

namespace CollatzMoonshot

open MeasureTheory

noncomputable instance : MeasurableSpace ℤ_[2] := borel ℤ_[2]

instance : BorelSpace ℤ_[2] := ⟨rfl⟩

/-- `T2`-invariance of a measure on `ℤ_[2]` (bundles measurability of `T2`). -/
def IsT2Invariant (μ : Measure ℤ_[2]) : Prop := MeasurePreserving T2 μ μ

/-- `T2` is Borel measurable - immediate from `continuous_T2`, and exactly the
measurability half of `IsT2Invariant`. -/
theorem measurable_T2 : Measurable T2 := continuous_T2.measurable

/-- With measurability discharged once and for all, `T2`-invariance is *only*
push-forward equality - the form every transfer argument (M2) actually uses. -/
theorem isT2Invariant_iff_map_eq {μ : Measure ℤ_[2]} :
    IsT2Invariant μ ↔ Measure.map T2 μ = μ :=
  ⟨fun h => h.map_eq, fun h => ⟨measurable_T2, h⟩⟩

/-- The embedded trivial cycle `{1, 2, 4} ⊆ ℤ_[2]`. -/
def trivialCycleZ2 : Set ℤ_[2] := {1, 2, 4}

/-- The 2-adic closure of the embedded orbit of `n`. -/
def orbitClosure (n : ℕ) : Set ℤ_[2] :=
  closure (Set.range fun k => ((step^[k] n : ℕ) : ℤ_[2]))

/-- **W1, the lane keystone (PROGRAM-grade working conjecture - ours, so a `def`,
never an `axiom`)**: every `T2`-invariant Borel probability measure supported on
the 2-adic closure of a positive Collatz orbit gives the embedded trivial cycle
positive mass.

Status and honesty ledger:
* Consistent with the conjectured world: if Collatz holds, every orbit closure is
  a finite set whose invariant measures concentrate on the trivial cycle.  W1 is
  the assertion that the arithmetic conditioning forces cycle-charging *without*
  assuming Collatz.
* Teeth: by the funnel (`Rigidity/Funnel.lean`), charging the trivial cycle means
  2-adic returns near `1` at all scales with positive frequency, and each return
  is a `(3/4)^s` archimedean crash - divergence and cycle-charging are enemies.
* Owed (milestone M2): `W1 → NoDivergentOrbit`, via Krylov-Bogolyubov transfer
  (THEOREM-grade, axiomatizable when needed) plus the frequency/all-scales
  upgrade of the funnel.  Then `conjecture_of_fronts` closes the loop:
  rigidity + no-cycles ⟹ Collatz.
* The statement may evolve as the lane learns; it is a pin, not a claim. -/
def MeasureRigidityW1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ μ : Measure ℤ_[2], IsProbabilityMeasure μ →
    IsT2Invariant μ → μ (orbitClosure n) = 1 → 0 < μ trivialCycleZ2

/-! ## W1′: the parity form of the keystone

W1 buys a *qualitative* fact - some invariant mass sits on the trivial cycle -
and M2 then has to convert that into "the orbit cannot run away", by upgrading
the pointwise funnel to a frequency statement at all 2-adic scales.  That
conversion is where the lane is expensive: returns to depth `s` have frequency
about `4⁻ˢ`, so they are separated by about `4ˢ` steps, over which the orbit may
grow by far more than the `(3/4)ˢ` a single return wins back.  Positive mass near
the cycle is a weak currency.

W1′ changes the currency.  `Rigidity/Drift.lean` shows that the quantity
controlling archimedean size is the **odd-step frequency**, and
`isClopen_evenSet` shows the parity partition is clopen upstairs - so
`μ ↦ μ oddSetZ2` is weak-* continuous, and the empirical odd frequency of an
orbit converges to it along any orbit-limit measure (Portmanteau on a continuity
set, whose boundary here is literally empty).  A bound on that one number is
already descent, with no funnel-frequency upgrade owed. -/

/-- The odd (unit) part of `ℤ_[2]`: the parity partition upstairs. -/
def oddSetZ2 : Set ℤ_[2] := {x : ℤ_[2] | (2 : ℤ_[2]) ∣ x}ᶜ

/-- The parity partition is clopen, which is exactly why its measure survives a
weak-* limit. -/
theorem isClopen_oddSetZ2 : IsClopen oddSetZ2 := isClopen_evenSet.compl

/-- **W1′, the parity form of the lane keystone (PROGRAM-grade working conjecture
- ours, so a `def`, never an `axiom`)**: every `T2`-invariant Borel probability
measure supported on the 2-adic closure of a positive Collatz orbit gives the odd
set mass strictly below the sharp drift threshold `log 2 / log 6`.

Status and honesty ledger:
* **Consistent with the conjectured world**: if Collatz holds, every orbit closure
  is finite, so invariant measures concentrate on the recurrent part `{1, 2, 4}`,
  where the odd frequency is exactly `1/3 < log 2 / log 6`.
* **The conditioning is load-bearing and provably so**: the `ℤ_[2]` 2-cycle
  `-1 → -2 → -1` (`T2_neg_cycle`) carries an invariant measure with odd mass
  `1/2`, above the threshold.  So the unconditioned statement is *false*, exactly
  as for W1 - the support hypothesis is where "arises from ℕ" enters.
* **Owed (milestone M2′)**: `ParityRigidityW1' → NoDivergentOrbit`, via
  Krylov-Bogolyubov transfer (THEOREM-grade, axiomatizable) + Portmanteau on the
  clopen parity set + `lt_of_oddSteps_freq_lt`.  The floor `N` in the drift
  estimate is supplied by the divergence itself, and `tendsto_freqThreshold` is
  what makes the sharp constant the right target.
* **W1 is not retired.**  It carries a mechanism (the funnel) that W1′ does not,
  and M3 may want it.  Both are pins, not claims. -/
def ParityRigidityW1' : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ μ : Measure ℤ_[2], IsProbabilityMeasure μ →
    IsT2Invariant μ → μ (orbitClosure n) = 1 → (μ oddSetZ2).toReal < sharpThreshold

end CollatzMoonshot
