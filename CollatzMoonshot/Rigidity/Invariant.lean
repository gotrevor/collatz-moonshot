/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.Rigidity.Padic

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

end CollatzMoonshot
