/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.FrontB.Words

/-!
# The negative side: a falsification harness for Front B 🚨

The `3n+1` map extends verbatim to `ℤ`, and on the negatives it **has** nontrivial cycles:
`−1`, `−5` and `−17` each sit on one.  The word formalism carries over unchanged, with
`den = 2^k − 3^x < 0`.

**Therefore any argument for Front B that does not consume the sign is wrong.**  This is the
3x−1 barrier of `APPROACHES.md` in executable form: before believing a lemma about positive
cycles, run it against `-1`, `-5`, `-17`.  A proof that survives here has failed.

The `−17` cycle takes 18 steps of which 7 are odd, so in the shortcut/word encoding it is
`(k, x) = (11, 7)` with `den = 2^11 − 3^7 = −139` - exactly the pair at which a brute-force
count over words finds 11 integral solutions, one per rotation.  The counting machinery sees
cycles when cycles exist.
-/

namespace CollatzMoonshot.FrontB

/-- The Collatz map on `ℤ`, same formula as on `ℕ`. -/
def stepZ (n : ℤ) : ℤ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `n` lies on a cycle of the integer Collatz map. -/
def OnCycleZ (n : ℤ) : Prop := ∃ m, 0 < m ∧ stepZ^[m] n = n

theorem cycle_neg_one : stepZ^[2] (-1) = -1 := by decide

theorem cycle_neg_five : stepZ^[5] (-5) = -5 := by decide

theorem cycle_neg_seventeen : stepZ^[18] (-17) = -17 := by decide

theorem onCycleZ_neg_one : OnCycleZ (-1) := ⟨2, by norm_num, cycle_neg_one⟩
theorem onCycleZ_neg_five : OnCycleZ (-5) := ⟨5, by norm_num, cycle_neg_five⟩
theorem onCycleZ_neg_seventeen : OnCycleZ (-17) := ⟨18, by norm_num, cycle_neg_seventeen⟩

/-- The three negative cycles are genuinely distinct orbits. -/
theorem neg_cycles_distinct :
    stepZ^[5] (-1) ≠ -5 ∧ stepZ^[18] (-5) ≠ -17 := by decide

/-- **The falsification harness.**  Nontrivial integer cycles exist.  Any Front B argument
that would also establish this is unsound, so every candidate lemma must be checked for
where it uses positivity. -/
theorem exists_nontrivial_cycleZ : ∃ n : ℤ, n < 0 ∧ OnCycleZ n :=
  ⟨-17, by norm_num, onCycleZ_neg_seventeen⟩

/-- The `−17` cycle's word data: `2^11 − 3^7 = −139`. -/
theorem den_neg_seventeen : (2:ℤ) ^ 11 - 3 ^ 7 = -139 := by norm_num

end CollatzMoonshot.FrontB
