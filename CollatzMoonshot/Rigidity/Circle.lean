/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The ×2,×3 circle vocabulary and the Rudolph-Johnson statement

The rigidity lane's model theorems live on the circle: Furstenberg's topological
×2×3 rigidity (axiomatized in `Assumed/Furstenberg.lean`) and the Rudolph-Johnson
measure rigidity theorem.

**Rudolph-Johnson is stated here PARAMETERIZED by an entropy functional** rather
than axiomatized outright: mathlib has topological entropy but no Kolmogorov-Sinai
(measure) entropy yet, and an axiom quantifying over an *opaque* entropy constant
would be potentially vacuous - formalization theater.  `RudolphJohnsonStatement h`
is honest vocabulary: for the intended `h` it *is* the Rudolph-Johnson theorem
(1990, with Johnson's ×p,×q extension).  Named blocker: **KS entropy in mathlib**;
when it lands, instantiate, axiomatize THEOREM-grade (or prove, someday), and
retire the parameter.
-/

namespace CollatzMoonshot

open MeasureTheory
open scoped ENNReal

/-- The doubling map on the unit circle `ℝ/ℤ`. -/
def circleDouble (x : UnitAddCircle) : UnitAddCircle := x + x

/-- The tripling map on the unit circle `ℝ/ℤ`. -/
def circleTriple (x : UnitAddCircle) : UnitAddCircle := x + x + x

/-- Ergodicity for the joint ×2,×3 semigroup action: any measurable set invariant
under BOTH maps is null or conull.  (Strictly stronger than ergodicity of either
map alone being assumed for the pair - this is the hypothesis Rudolph-Johnson
actually uses.) -/
def JointlyErgodic₂₃ (μ : Measure UnitAddCircle) : Prop :=
  ∀ s : Set UnitAddCircle, MeasurableSet s →
    circleDouble ⁻¹' s = s → circleTriple ⁻¹' s = s → μ s = 0 ∨ μ sᶜ = 0

/-- **The Rudolph-Johnson theorem, parameterized by an entropy functional**: a
×2,×3-jointly-invariant, jointly-ergodic probability measure with positive entropy
under doubling is the Haar (Lebesgue) measure.  For the intended Kolmogorov-Sinai
`entropy` this is a published theorem (Rudolph 1990, Johnson 1992); the parameter
exists only because mathlib lacks KS entropy (see module docstring).  The
zero-entropy case is Furstenberg's ×2×3 conjecture - OPEN, and the reason this
lane may be Furstenberg-hard. -/
def RudolphJohnsonStatement
    (entropy : Measure UnitAddCircle → (UnitAddCircle → UnitAddCircle) → ℝ≥0∞) :
    Prop :=
  ∀ μ : Measure UnitAddCircle, IsProbabilityMeasure μ →
    MeasurePreserving circleDouble μ μ → MeasurePreserving circleTriple μ μ →
    JointlyErgodic₂₃ μ → 0 < entropy μ circleDouble → μ = volume

end CollatzMoonshot
