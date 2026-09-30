/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import MSP2.Hypothesis

/-!
# MSP²: the headline

`conjecture_of_raccord` is the article's conditional conclusion made formal: the open
step implies the Collatz conjecture (§16.2 "De la couverture à l'arrivée à 1", §20).

`raccord_of_conjecture` is the converse, and together they give `raccord_iff_conjecture`:
the remaining step, read as §16.2 states it, is *equivalent* to the Collatz conjecture.
That is not a defect of the reading - "every `N ≥ 2` eventually dips below itself" is
Terras's classical reformulation (`CollatzMoonshot.conjecture_iff_descent`).  It locates
where the difficulty lives: any proof of `Raccord` is a proof of Collatz, so the value of
the Generator Table machinery is whatever finer, checkable statement the authors can put
beneath `Raccord`.
-/

namespace MSP2

open CollatzMoonshot

theorem raccord_iff_descent : Raccord ↔ DescentAll := by
  constructor
  · intro h N hN
    exact h N N hN (by
      have : N < 2 ^ N := Nat.lt_two_pow_self
      omega)
  · intro h n N hN _
    exact h N hN

/-- **Headline**: the open step implies the Collatz conjecture. -/
theorem conjecture_of_raccord (h : Raccord) : Conjecture :=
  conjecture_of_descent (raccord_iff_descent.mp h)

/-- **Converse**: the Collatz conjecture implies the open step. -/
theorem raccord_of_conjecture (h : Conjecture) : Raccord :=
  raccord_iff_descent.mpr (descent_of_conjecture h)

/-- The open step, read as §16.2 states it, is exactly the Collatz conjecture. -/
theorem raccord_iff_conjecture : Raccord ↔ Conjecture :=
  ⟨conjecture_of_raccord, raccord_of_conjecture⟩

end MSP2
