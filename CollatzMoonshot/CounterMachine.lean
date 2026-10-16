/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Counter machines in Morita's quadruple format

The shared format for the two halves of "halting is undecidable for valid reversible 2-counter
machines" (`RcwaSameOrbit.HaltingUndecidable`).  Source: Morita, *Theory of Reversible Computing*
(2017), §9.2.

1. **Quadruples (Def 9.1).**  A rule is `[p, i, Z|P, q]` (test counter `i`) or `[p, i, −|0|+, q]`
   (count).  `Op` is the middle part: `test i pos` (`pos = false` reads `Z`, `true` reads `P`),
   `dec i`, `inc i`, `nop` (Morita's `[p, i, 0, q]`, whose counter index is irrelevant).  The
   counters are indexed by an arbitrary type `ι`, the states by an arbitrary type `Q`, and a
   machine `CM Q ι` is a *set* of quadruples.
2. **Semantics (Def 9.3).**  `Op.Act` is the counter relation (a decrement needs a positive
   counter), `CM.Step` the transition relation on `Cfg Q ι = Q × (ι → ℕ)`, `CM.Halts` reaching a
   halting ID (any configuration with no successor; no final states).
3. **Determinism and reversibility (Def 9.2), syntactic.**  Two distinct rules from (into) one
   state are both tests of the same counter with different symbols.  These imply the semantic
   versions on *all* configurations (`step_functional`, `step_injective`).
4. **Normal form (Def 9.4)**, only the half that matters: the initial state is the target of no
   rule (`NormalAt`), so every configuration in it is a source.  `RevMortal`: no infinite backward
   chain from any configuration (Kari–Ollinger's mortal reverse).
5. **The interface Prop `UndecidableCM`.**  One fixed deterministic machine whose halting problem,
   on inputs `n ↦ (q₀, enc n in counter i₀, 0, …, 0)` with `enc` computable, is not computable.
   `CounterMachineUniversal` proves it from Mathlib's halting problem; `RcwaHalting` turns it into
   `RcwaSameOrbit.HaltingUndecidable`.
-/

namespace CollatzMoonshot.CounterMachine

/-! ## 1. Quadruples -/

/-- The operation of a Morita quadruple: a test (`pos = false` reads `Z`, `true` reads `P`), a
decrement, an increment, or no move. -/
inductive Op (ι : Type*) where
  | test (i : ι) (pos : Bool)
  | dec (i : ι)
  | inc (i : ι)
  | nop
  deriving DecidableEq, Fintype

namespace Op

variable {ι ι' : Type*}

/-- Relabel the counters. -/
def map (f : ι → ι') : Op ι → Op ι'
  | test i b => test (f i) b
  | dec i => dec (f i)
  | inc i => inc (f i)
  | nop => nop

/-- Morita's inverse operation `x⁻¹`: tests are self-inverse, `−` and `+` swap. -/
def inv : Op ι → Op ι
  | test i b => test i b
  | dec i => inc i
  | inc i => dec i
  | nop => nop

/-- The counter relation (Def 9.3): `Act v w` when the operation takes the counters `v` to `w`.
A test needs the right zero-ness and changes nothing; a decrement needs a positive counter. -/
def Act : Op ι → (ι → ℕ) → (ι → ℕ) → Prop
  | test i b, v, w => decide (0 < v i) = b ∧ w = v
  | dec i, v, w => 0 < v i ∧ w i + 1 = v i ∧ ∀ j, j ≠ i → w j = v j
  | inc i, v, w => w i = v i + 1 ∧ ∀ j, j ≠ i → w j = v j
  | nop, v, w => w = v

/-- The change an operation makes to counter `j` (for lap vectors). -/
def delta [DecidableEq ι] : Op ι → ι → ℤ
  | dec i, j => if j = i then -1 else 0
  | inc i, j => if j = i then 1 else 0
  | _, _ => 0

/-- An operation's counter relation is functional. -/
theorem act_functional {o : Op ι} {v w w' : ι → ℕ}
    (h : o.Act v w) (h' : o.Act v w') : w = w' := by
  sorry

/-- An operation's counter relation is injective. -/
theorem act_injective {o : Op ι} {v v' w : ι → ℕ}
    (h : o.Act v w) (h' : o.Act v' w) : v = v' := by
  sorry

/-- The inverse operation is the converse relation. -/
theorem act_inv {o : Op ι} {v w : ι → ℕ} :
    o.inv.Act w v ↔ o.Act v w := by
  sorry

end Op

/-- A Morita quadruple `[src, op, dst]`. -/
structure Quad (Q ι : Type*) where
  /-- The state the rule leaves. -/
  src : Q
  /-- The operation. -/
  op : Op ι
  /-- The state the rule enters. -/
  dst : Q
  deriving DecidableEq, Fintype

/-- The inverse quadruple `[dst, op⁻¹, src]` (Morita, Lemma 9.4, stage 3). -/
def Quad.inv {Q ι : Type*} (ρ : Quad Q ι) : Quad Q ι :=
  ⟨ρ.dst, ρ.op.inv, ρ.src⟩

/-- A configuration (Morita's ID): a state and the counters. -/
abbrev Cfg (Q ι : Type*) : Type _ := Q × (ι → ℕ)

/-- A counter machine: a set of quadruples. -/
abbrev CM (Q ι : Type*) : Type _ := Set (Quad Q ι)

namespace CM

variable {Q ι : Type*}

/-- One transition (Def 9.3). -/
def Step (M : CM Q ι) (c d : Cfg Q ι) : Prop :=
  ∃ ρ ∈ M, c.1 = ρ.src ∧ d.1 = ρ.dst ∧ ρ.op.Act c.2 d.2

/-- Reachability, `|−*`. -/
def Reaches (M : CM Q ι) : Cfg Q ι → Cfg Q ι → Prop :=
  Relation.ReflTransGen M.Step

/-- A halting ID: no successor. -/
def Stuck (M : CM Q ι) (c : Cfg Q ι) : Prop :=
  ∀ d, ¬ M.Step c d

/-- The run from `c` halts: it reaches a halting ID. -/
def Halts (M : CM Q ι) (c : Cfg Q ι) : Prop :=
  ∃ d, M.Reaches c d ∧ M.Stuck d

/-- `c` has no predecessor. -/
def IsSource (M : CM Q ι) (c : Cfg Q ι) : Prop :=
  ∀ d, ¬ M.Step d c

/-- **Determinism (Def 9.2).**  Two distinct rules from one state are tests of one counter with
different symbols. -/
def Det (M : CM Q ι) : Prop :=
  ∀ ρ ∈ M, ∀ ρ' ∈ M, ρ ≠ ρ' → ρ.src = ρ'.src →
    ∃ i b b', ρ.op = .test i b ∧ ρ'.op = .test i b' ∧ b ≠ b'

/-- **Reversibility (Def 9.2).**  Two distinct rules into one state are tests of one counter with
different symbols. -/
def Rev (M : CM Q ι) : Prop :=
  ∀ ρ ∈ M, ∀ ρ' ∈ M, ρ ≠ ρ' → ρ.dst = ρ'.dst →
    ∃ i b b', ρ.op = .test i b ∧ ρ'.op = .test i b' ∧ b ≠ b'

/-- **Normal form at `q₀` (Def 9.4, first half).**  No rule enters `q₀`. -/
def NormalAt (M : CM Q ι) (q₀ : Q) : Prop :=
  ∀ ρ ∈ M, ρ.dst ≠ q₀

/-- **Mortal reverse.**  No infinite backward chain, from any configuration (in particular no
cycle). -/
def RevMortal (M : CM Q ι) : Prop :=
  ¬ ∃ x : ℕ → Cfg Q ι, ∀ n, M.Step (x (n + 1)) (x n)

/-- The machine on the subtype of `S`: the rules with both ends in `S`. -/
def restrict (M : CM Q ι) (S : Set Q) : CM S ι :=
  {ρ | (⟨ρ.src.1, ρ.op, ρ.dst.1⟩ : Quad Q ι) ∈ M}

/-! ## 2. Sanity lemmas -/

/-- Syntactic determinism gives a functional step on every configuration. -/
theorem step_functional {M : CM Q ι} (hM : M.Det) {c d d' : Cfg Q ι} (h : M.Step c d)
    (h' : M.Step c d') : d = d' := by
  sorry

/-- Syntactic reversibility gives an injective step on every configuration. -/
theorem step_injective {M : CM Q ι} (hM : M.Rev) {c c' d : Cfg Q ι} (h : M.Step c d)
    (h' : M.Step c' d) : c = c' := by
  sorry

/-- In normal form every configuration at `q₀` is a source. -/
theorem isSource_of_normalAt {M : CM Q ι} {q₀ : Q} (hM : M.NormalAt q₀) (v : ι → ℕ) :
    M.IsSource (q₀, v) := by
  sorry

/-- A deterministic machine with an infinite run from `c` does not halt from `c`. -/
theorem not_halts_of_forever {M : CM Q ι} (hM : M.Det) (x : ℕ → Cfg Q ι)
    (hx : ∀ n, M.Step (x n) (x (n + 1))) : ¬ M.Halts (x 0) := by
  sorry

/-- **Simulation.**  Let `Sim c c'` relate configurations of `M` and of a deterministic `M'`.
If every step of `M` from a related `c` is matched by a nonempty run of `M'` to a related
configuration, and `M'` halts from every configuration related to a halting ID of `M`, then `M'`
halts from `c'` exactly when `M` halts from `c`. -/
theorem halts_iff_of_sim {Q' ι' : Type*} {M : CM Q ι} {M' : CM Q' ι'} (hdet : M'.Det)
    (Sim : Cfg Q ι → Cfg Q' ι' → Prop)
    (hstep : ∀ c d c', M.Step c d → Sim c c' → ∃ d', Relation.TransGen M'.Step c' d' ∧ Sim d d')
    (hstuck : ∀ c c', M.Stuck c → Sim c c' → M'.Halts c') {c : Cfg Q ι} {c' : Cfg Q' ι'}
    (h : Sim c c') : M'.Halts c' ↔ M.Halts c := by
  sorry

/-- Restriction keeps determinism. -/
theorem restrict_det {M : CM Q ι} (hM : M.Det) (S : Set Q) : (M.restrict S).Det := by
  sorry

/-- Restriction keeps the normal form. -/
theorem restrict_normalAt {M : CM Q ι} {q₀ : Q} (hM : M.NormalAt q₀) (S : Set Q)
    (hq₀ : q₀ ∈ S) : (M.restrict S).NormalAt ⟨q₀, hq₀⟩ := by
  sorry

/-- Restricting to a set closed under the rules does not change halting. -/
theorem halts_restrict {M : CM Q ι} {S : Set Q} (hS : ∀ ρ ∈ M, ρ.src ∈ S → ρ.dst ∈ S)
    {q : Q} (hq : q ∈ S) (v : ι → ℕ) :
    (M.restrict S).Halts (⟨q, hq⟩, v) ↔ M.Halts (q, v) := by
  sorry

end CM

/-! ## 3. The interface -/

open Classical in
/-- **The interface between the two halves.**  One fixed deterministic counter machine `M`
(finitely many states and counters, normal form at `q₀`) and a computable `enc` such that
halting of `M` from `q₀` with `enc n` in counter `i₀` and every other counter `0` is not a
computable predicate of `n`. -/
def UndecidableCM : Prop :=
  ∃ (Q ι : Type) (_ : Finite Q) (_ : Finite ι) (M : CM Q ι) (q₀ : Q) (i₀ : ι) (enc : ℕ → ℕ),
    M.Det ∧ M.NormalAt q₀ ∧ Computable enc ∧
      ¬ ComputablePred fun n => M.Halts (q₀, Pi.single i₀ (enc n))

end CollatzMoonshot.CounterMachine
