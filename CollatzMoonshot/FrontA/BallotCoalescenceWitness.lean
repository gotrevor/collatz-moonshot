/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.FirstCrossing

/-!
# Ballot coalescence: the refuted rigidity, as a witness

Two starts whose first `34` parity letters are both prefix-supercritical ("ballot": every prefix
`j` has `2^j ≤ 3^(ones)`), with the same number of odd steps, can reach the same value after
`34` steps.  So the conjecture "every integer has at most one ballot ancestor per shape" (the
ballot-coalescence rigidity of 2026-09-19, motivated by a zero count at every length up to 30)
is false; equivalently, a ballot word's numerator need not be the least in its residue class
mod `3^ones`.  Found by the Φ-walk probe `experiments/parity_reconstruction.py ballot-walk 34 4`
(2026-09-19); the pair is re-verified there by direct iteration.  The record is the retired list
in `DIRECTION.md` and the personal KB leaf `collatz-ballot-coalescence-2026-09-19.md`.

The consequence for the first-crossing route: the least coefficient-stopping-time failure
cannot have, as a prefix of its word, the smaller-numerator member of such a pair (the smaller
start would survive its first crossing too), a real but thin constraint.
-/

namespace CollatzMoonshot.FrontA.FirstCrossing

open CollatzMoonshot CollatzMoonshot.FrontB

/-- Every prefix of the first `m` letters of the parity trace of `n`, including the whole word,
has coefficient at least one. -/
def BallotTo (n m : ℕ) : Prop := ∀ j ≤ m, 2 ^ j ≤ 3 ^ ones (traceWord n j)

instance (n m : ℕ) : Decidable (BallotTo n m) := by unfold BallotTo; infer_instance

/-- `15231450875` and `15231450879` both have ballot words of length `34` with `22` odd steps,
the words differ, and the two orbits meet after `34` steps (at `27822043514`). -/
theorem ballot_coalescence_witness :
    BallotTo 15231450875 34 ∧ BallotTo 15231450879 34 ∧
    ones (traceWord 15231450875 34) = 22 ∧ ones (traceWord 15231450879 34) = 22 ∧
    traceWord 15231450875 34 ≠ traceWord 15231450879 34 ∧
    tstep^[34] 15231450875 = tstep^[34] 15231450879 := by
  native_decide

/-- The rigidity, stated as it was conjectured ("at most one ballot ancestor per shape"), is
false. -/
theorem not_ballot_ancestor_unique :
    ¬ ∀ x x' m : ℕ, BallotTo x m → BallotTo x' m →
      ones (traceWord x m) = ones (traceWord x' m) → tstep^[m] x = tstep^[m] x' → x = x' := by
  intro h
  have := h 15231450875 15231450879 34 ballot_coalescence_witness.1
    ballot_coalescence_witness.2.1
    (by rw [ballot_coalescence_witness.2.2.1, ballot_coalescence_witness.2.2.2.1])
    ballot_coalescence_witness.2.2.2.2.2
  omega

end CollatzMoonshot.FrontA.FirstCrossing
