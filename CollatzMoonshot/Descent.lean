/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Conjecture

/-!
# Descent: the classical reformulation, and the lane consumption forms

`DescentAll` (every `n ≥ 2` eventually dips below itself - Terras's "finite
stopping time for all `n`") is equivalent to the conjecture by strong induction,
with no cycle hypothesis needed.  It is the cleanest single statement a
divergence-killing lane can aim at: descent needs no separate cycle argument.

`conjecture_of_fronts` is the other consumption form: Front A + Front B ⟹
Collatz, the packaging of `conjecture_iff_split` a rigidity lane consumes when it
proves `NoDivergentOrbit` and hands cycles to the arithmetic lane.
-/

namespace CollatzMoonshot

/-- **Descent**: every `n ≥ 2` eventually dips strictly below its starting value.
(Any witnessing `k` is automatically positive.) -/
def DescentAll : Prop := ∀ n, 2 ≤ n → ∃ k, step^[k] n < n

/-- Descent implies the conjecture, by strong induction: dip below `n`, land on a
positive smaller value, recurse. -/
theorem conjecture_of_descent (h : DescentAll) : Conjecture := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases eq_or_lt_of_le hn with h1 | h2
    · exact h1 ▸ reachesOne_one
    · obtain ⟨k, hk⟩ := h n h2
      have hm1 : 1 ≤ step^[k] n := iterate_step_pos hn k
      obtain ⟨c, hc⟩ := ih (step^[k] n) hk hm1
      exact ⟨c + k, by rw [Function.iterate_add_apply, hc]⟩

theorem descent_of_conjecture (h : Conjecture) : DescentAll := by
  intro n hn
  obtain ⟨k, hk⟩ := h n (by omega)
  exact ⟨k, by omega⟩

/-- The conjecture IS universal descent - so a lane that proves descent needs no
separate cycle argument at all. -/
theorem conjecture_iff_descent : Conjecture ↔ DescentAll :=
  ⟨descent_of_conjecture, conjecture_of_descent⟩

/-- **The two-front consumption form**: what the rigidity lane (Front A) plus the
arithmetic lane (Front B) jointly deliver. -/
theorem conjecture_of_fronts (hA : NoDivergentOrbit) (hB : NoNontrivialCycle) :
    Conjecture :=
  conjecture_iff_split.mpr ⟨hA, hB⟩

end CollatzMoonshot
