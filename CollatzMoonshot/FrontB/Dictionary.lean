/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Conjecture
import CollatzMoonshot.FrontB.Words
import CollatzMoonshot.FrontB.Threads

/-!
# The dictionary: `NoNontrivialCycle` (on `ℕ`) ↔ `FrontB` (on words)

The Halbeisen-Hungerbühler / Bernstein-Lagarias correspondence.  Until this file is
sorry-free, everything in `FrontB/` is a statement about words, not about Collatz on `ℕ`
(see the warning in `FrontB/Threads.lean`).  Landing this bridge retroactively upgrades
every `FrontB/` theorem to a genuine Collatz statement.

## Structure

The word convention in `Words.lean` (`den v = 2^|v| − 3^(ones v)`) matches the
**accelerated** (Syracuse-style) map `tstep` - every step halves once, odd steps also
multiply by 3 - not the un-accelerated `step` of `Basic.lean`.  So the bridge has two
layers:

1. **orbit ↔ word** (`tstep`-cycles ↔ words): the parity trace of a `tstep`-cycle through
   `n` is a word `v` with `(n : ℤ) * den v = numer v`.  Sanity anchors, hand-checked:
   `n = 1`, `v = [true, false]`: `den = 1`, `numer = 1` ✓;
   `n = 2`, `v = [false, true]`: `den = 1`, `numer = 2` ✓.
   (Orientation: the FIRST letter of the trace is the parity of `n` itself.)
   The engine is the exact rotation identity `two_mul_numer_rot_false/true` - one orbit
   step corresponds to one word rotation.
2. **`step` ↔ `tstep`** (un-accelerated ↔ accelerated cycles): in a `step`-cycle every odd
   step `n ↦ 3n+1` lands on an even number, so contracting each such pair yields a
   `tstep`-cycle on the odd-or-halving members; conversely a `tstep`-cycle expands.  The
   trivial `tstep`-cycle `{1, 2}` expands to the trivial `step`-cycle `{1, 2, 4}`.

## Contract for the treadmill 🎯

- The two HEADLINE theorems (`noNontrivialCycle_of_frontB`, `noNontrivialCycle_iff_frontB`)
  are **frozen statements** - guard them by name; do not weaken or restate them.  The
  MILESTONE lemmas between here and there are scaffolding: adjust their statements freely
  if a cleaner decomposition appears (fix hypotheses, reorient the trace, split further).
- **No new axioms anywhere in this file.**  This is our own target: every `sorry` must
  become a proof.  At the end, `#print axioms noNontrivialCycle_iff_frontB` must show at
  most `[propext, Classical.choice, Quot.sound]`.
-/

namespace CollatzMoonshot.FrontB

open CollatzMoonshot

/-! ## Layer 1: the accelerated map and its parity trace -/

/-- The accelerated (Syracuse-style) Collatz map: every application halves once.
This is the map whose cycles the words of `Words.lean` encode. -/
def tstep (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

@[simp] theorem tstep_one : tstep 1 = 2 := by decide

@[simp] theorem tstep_two : tstep 2 = 1 := by decide

/-- MILESTONE (adjustable).  The parity trace of the first `m` accelerated steps from `n`:
the first letter is the parity of `n` itself. -/
def traceWord (n : ℕ) : ℕ → List Bool
  | 0 => []
  | m + 1 => (n % 2 = 1) :: traceWord (tstep n) m

@[simp] theorem traceWord_length (n m : ℕ) : (traceWord n m).length = m := by
  induction m generalizing n with
  | zero => rfl
  | succ k ih => simp [traceWord, ih]

/-- MILESTONE (adjustable).  **The member identity**: if the accelerated orbit returns to
`n` after `m > 0` steps, the parity trace is a word `v` with `(n : ℤ) * den v = numer v`.
Engine: induction along the orbit via `two_mul_numer_rot_false/true` (one orbit step = one
word rotation). -/
theorem member_identity {n m : ℕ} (hn : 1 ≤ n) (hm : 0 < m)
    (hcyc : tstep^[m] n = n) :
    (n : ℤ) * den (traceWord n m) = (numer (traceWord n m) : ℤ) := by
  sorry

/-- MILESTONE (adjustable).  A nontrivial accelerated cycle has an odd member, so its
trace has a `true`.  (An all-halving cycle would strictly decrease.) -/
theorem ones_pos_of_cycle {n m : ℕ} (hn : 1 ≤ n) (hm : 0 < m)
    (hcyc : tstep^[m] n = n) : 1 ≤ ones (traceWord n m) := by
  sorry

/-- MILESTONE (adjustable).  The trace of an accelerated cycle is an `IntegerCycle`:
nonempty, has an odd step, positive denominator, and the divisibility - all falling out of
`member_identity`. -/
theorem integerCycle_traceWord {n m : ℕ} (hn : 1 ≤ n) (hm : 0 < m)
    (hcyc : tstep^[m] n = n) : IntegerCycle (traceWord n m) := by
  sorry

/-! ## Layer 2: un-accelerated ↔ accelerated cycles -/

/-- MILESTONE (adjustable).  A `step`-cycle through `n ≥ 1` yields an accelerated cycle
through a related member (contract each `odd, even` pair; if `n` is the `3k+1`-intermediate
of an odd member, pass to a genuine member of the accelerated cycle). -/
theorem tstep_cycle_of_step_cycle {n : ℕ} (hn : 1 ≤ n) (hc : OnCycle n) :
    ∃ n' m, 1 ≤ n' ∧ 0 < m ∧ tstep^[m] n' = n' ∧
      (n = n' ∨ n = 3 * n' + 1 ∨ ∃ j, tstep^[j] n' = n) := by
  sorry

/-- MILESTONE (adjustable).  If the accelerated cycle through `n'` is trivial
(`n' = 1`), the `step`-cycle members it came from are among `{1, 2, 4}`. -/
theorem step_member_trivial {n n' : ℕ} (hn : 1 ≤ n) (hc : OnCycle n)
    (h1 : n' = 1) (hrel : n = n' ∨ n = 3 * n' + 1 ∨ ∃ j, tstep^[j] n' = n) :
    n = 1 ∨ n = 2 ∨ n = 4 := by
  sorry

/-! ## Headlines - FROZEN statements 🧊 -/

/-- **HEADLINE (frozen).**  The word-level Front B implies the `ℕ`-level one: if every
integral positive word-cycle is trivial, then every Collatz cycle is the trivial one.
This is the direction that upgrades every `FrontB/` theorem to a Collatz statement. -/
theorem noNontrivialCycle_of_frontB (h : FrontB) : NoNontrivialCycle := by
  sorry

/-- MILESTONE (adjustable).  The converse: an `IntegerCycle` word is realized by an actual
accelerated `ℕ`-cycle (its member is `numer v / den v`; the orbit follows the word), which
expands to a `step`-cycle; `NoNontrivialCycle` then forces triviality of the word. -/
theorem frontB_of_noNontrivialCycle (h : NoNontrivialCycle) : FrontB := by
  sorry

/-- **HEADLINE (frozen).**  The dictionary. -/
theorem noNontrivialCycle_iff_frontB : NoNontrivialCycle ↔ FrontB :=
  ⟨frontB_of_noNontrivialCycle, noNontrivialCycle_of_frontB⟩

end CollatzMoonshot.FrontB
