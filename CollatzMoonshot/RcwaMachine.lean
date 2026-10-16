/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Theorem C, the machine-to-permutation core: completion and Lemma M (abstract)

Two abstract pieces of the undecidability route for orbit counts of RCWA permutations of `ℤ`
(research notes `undec-lemma`, `undec-r25`).  No number theory appears here: the RCWA encoding
(Lemma P) turns a reversible counter machine into a partial injection, and these lemmas say what
the orbits of the completed permutation are.

## 1. Completion (Lemma C of `undec-lemma`, abstract form)

`f : PEquiv α α` is the configuration graph of a reversible machine (out- and in-degree `≤ 1`).
Its *sources* have no predecessor, its *sinks* no successor.  A bijection `τ : sinks ≃ sources`
and a *highway* type `H` are given, with a bijection `θ : ℤ ≃ sources ⊕ H` (the line).  The
completed map `σ` on `α ⊕ H` is

* `f` where `f` is defined,
* `ν ∘ τ` on sinks, where `ν = θ ∘ (+1) ∘ θ⁻¹` is the highway shift,
* `ν` on `H`.

`σ` is a bijection with no further hypotheses (`completeFun_bijective`).  Under

* **(H1)** no bi-infinite `f`-chain (a cycle is a periodic bi-infinite chain, so this also
  excludes cycles), and
* **(H2)** `τ (end x) = x` for every source `x` whose forward chain is finite,

the orbits of `σ` are the maximal cut-free runs of the line, where a *cut* is a source with an
infinite forward chain: `#orbits = 1 + #cuts` (`card_orbits`).  So `σ` has one orbit iff there is
no cut, and infinitely many orbits iff there are infinitely many cuts.  In the concrete build
each forward-divergent configuration comes with an infinite family of junk copies, so the count
is `1` or `∞`; that multiplicity is a property of the encoding, not of this lemma.

## 2. Lemma M (abstract)

A run of any step relation on `Q × V` (`Q` finite, `V` well-quasi-ordered, e.g. `ℕ × ℕ`) that
stays off a set `B` of boundary states and returns to a state must strictly lose (forward) or
gain (backward) in the order on `V`; then every infinite run visits `B` infinitely often
(`visits_boundary_forward`, `visits_boundary_backward`), by Dickson's lemma.  For a 2-counter
guarded machine the hypothesis follows from the paper's loop condition (S1), stated as: every
closed rule walk off `B` has a lap vector with one negative and one positive entry
(`TwoCounter.visits_boundary`).  Consequently immortality (and immortality of the reverse) is
decided by the macro map on boundary configurations (`immortal_iff_macro`,
`reverse_immortal_iff_macro`).
-/

namespace CollatzMoonshot.RcwaMachine

/-! ## 1. Completion -/

section Completion

universe u

variable {α H : Type u}

/-- The `n`-fold forward iterate of a partial injection, starting from `x`. -/
def fwd (f : PEquiv α α) (n : ℕ) (x : α) : Option α :=
  (fun o : Option α => o.bind f)^[n] (some x)

/-- Sources: configurations with no predecessor. -/
def Src (f : PEquiv α α) : Type u := {x : α // f.symm x = none}

/-- Sinks: configurations with no successor. -/
def Snk (f : PEquiv α α) : Type u := {x : α // f x = none}

/-- The forward chain from `x` is infinite. -/
def Diverges (f : PEquiv α α) (x : α) : Prop := ∀ n, fwd f n x ≠ none

/-- **(H1)** No bi-infinite chain: no `g : ℤ → α` with `f (g i) = g (i + 1)` for all `i`.
A cycle is a periodic such `g`, so this also rules out cycles. -/
def NoBiInfinite (f : PEquiv α α) : Prop :=
  ∀ g : ℤ → α, ¬ ∀ i, f (g i) = some (g (i + 1))

/-- **(H2)** The pairing returns every finite chain to its own start: if the chain from the source
`s` reaches the sink `t`, then `τ t = s`. -/
def EndToStart (f : PEquiv α α) (τ : Snk f ≃ Src f) : Prop :=
  ∀ (s : Src f) (t : Snk f) (n : ℕ), fwd f n s.1 = some t.1 → τ t = s

/-- The line points `sources ⊕ H`, viewed inside `α ⊕ H`. -/
def lineEmb (f : PEquiv α α) : Src f ⊕ H → α ⊕ H :=
  Sum.map Subtype.val id

/-- The highway shift `ν = θ ∘ (+1) ∘ θ⁻¹`, landing in `α ⊕ H`. -/
def nu (f : PEquiv α α) (θ : ℤ ≃ Src f ⊕ H) (p : Src f ⊕ H) : α ⊕ H :=
  lineEmb f (θ (θ.symm p + 1))

/-- The completed map: `f` where defined, `ν ∘ τ` on sinks, `ν` on the highway. -/
def completeFun (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H) :
    α ⊕ H → α ⊕ H
  | Sum.inl x =>
    match hx : f x with
    | some y => Sum.inl y
    | none => nu f θ (Sum.inl (τ ⟨x, hx⟩))
  | Sum.inr h => nu f θ (Sum.inr h)

/-- Part 1 of Lemma C: the completion is a bijection, for any partial injection `f`, any
bijection `τ` and any line `θ`. -/
theorem completeFun_bijective (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H) :
    Function.Bijective (completeFun f τ θ) := by
  sorry

/-- The completed permutation `σ` of `α ⊕ H`. -/
noncomputable def complete (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H) :
    Equiv.Perm (α ⊕ H) :=
  Equiv.ofBijective _ (completeFun_bijective f τ θ)

/-- The orbits of a permutation, as a quotient type. -/
abbrev Orbits {β : Type u} (σ : Equiv.Perm β) : Type u :=
  Quotient (Equiv.Perm.SameCycle.setoid σ)

/-- A non-divergent source at line position `p` lies on one orbit with line position `p + 1`:
`σ` runs its finite chain and, by (H2), returns to the highway at `ν` of the source. -/
theorem sameCycle_succ_of_not_diverges (f : PEquiv α α) (τ : Snk f ≃ Src f)
    (θ : ℤ ≃ Src f ⊕ H) (h2 : EndToStart f τ) (p : ℤ)
    (hp : ∀ s : Src f, θ p = Sum.inl s → ¬ Diverges f s.1) :
    (complete f τ θ).SameCycle (lineEmb f (θ p)) (lineEmb f (θ (p + 1))) := by
  sorry

/-- A divergent source at line position `p` is a cut: positions `≤ p` and `> p` lie on different
orbits.  Needs (H1) and (H2). -/
theorem not_sameCycle_of_cut (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ) (s : Src f) (hs : Diverges f s.1) {p q r : ℤ}
    (hp : θ p = Sum.inl s) (hq : q ≤ p) (hr : p < r) :
    ¬ (complete f τ θ).SameCycle (lineEmb f (θ q)) (lineEmb f (θ r)) := by
  sorry

/-- **Lemma C, orbit formula.**  Under (H1) and (H2), the number of orbits of the completion is
one more than the number of forward-divergent sources (as cardinals, so `1 + ℵ₀ = ℵ₀` covers the
infinite case). -/
theorem card_orbits (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ) :
    Cardinal.mk (Orbits (complete f τ θ)) = 1 + Cardinal.mk {s : Src f // Diverges f s.1} := by
  sorry

/-- One orbit iff no source diverges. -/
theorem sameCycle_all_iff (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ) :
    (∀ a b : α ⊕ H, (complete f τ θ).SameCycle a b) ↔ ∀ s : Src f, ¬ Diverges f s.1 := by
  sorry

/-- Infinitely many orbits iff infinitely many sources diverge. -/
theorem infinite_orbits_iff (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ) :
    Infinite (Orbits (complete f τ θ)) ↔ Infinite {s : Src f // Diverges f s.1} := by
  sorry

/-- **The `{1, ∞}` dichotomy.**  If divergent sources, when present, are infinitely many (the
junk multiplicity of the concrete encoding), the completion has one orbit or infinitely many;
it has one orbit exactly when no source diverges. -/
theorem one_or_infinite_orbits (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ)
    (hjunk : (∃ s : Src f, Diverges f s.1) → Infinite {s : Src f // Diverges f s.1}) :
    ((∀ a b : α ⊕ H, (complete f τ θ).SameCycle a b) ∧ ∀ s : Src f, ¬ Diverges f s.1) ∨
      (Infinite (Orbits (complete f τ θ)) ∧ ∃ s : Src f, Diverges f s.1) := by
  sorry

end Completion

/-! ## 2. Lemma M -/

section LemmaM

variable {Q V : Type*} [Preorder V]

/-- `x` steps from index `m` to index `n` and every state at indices `m, …, n` is off `B`. -/
def OffRun (B : Set Q) (Step : Q × V → Q × V → Prop) (x : ℕ → Q × V) (m n : ℕ) : Prop :=
  (∀ i, m ≤ i → i < n → Step (x i) (x (i + 1))) ∧ ∀ i, m ≤ i → i ≤ n → (x i).1 ∉ B

/-- Forward loop condition: a nonempty run off `B` that returns to its state never ends `≥` its
start in `V`.  For counters this says each lap decreases some counter. -/
def LapNotUp (B : Set Q) (Step : Q × V → Q × V → Prop) : Prop :=
  ∀ x m n, m < n → OffRun B Step x m n → (x m).1 = (x n).1 → ¬ (x m).2 ≤ (x n).2

/-- Backward loop condition: each such lap increases some counter. -/
def LapNotDown (B : Set Q) (Step : Q × V → Q × V → Prop) : Prop :=
  ∀ x m n, m < n → OffRun B Step x m n → (x m).1 = (x n).1 → ¬ (x n).2 ≤ (x m).2

/-- **Lemma M, forward.**  Every forward-infinite run visits `B` infinitely often. -/
theorem visits_boundary_forward [Finite Q] [WellQuasiOrderedLE V] (B : Set Q)
    (Step : Q × V → Q × V → Prop) (hlap : LapNotUp B Step) (x : ℕ → Q × V)
    (hx : ∀ n, Step (x n) (x (n + 1))) : ∀ N, ∃ n, N ≤ n ∧ (x n).1 ∈ B := by
  sorry

/-- **Lemma M, backward.**  Every backward-infinite run visits `B` infinitely often. -/
theorem visits_boundary_backward [Finite Q] [WellQuasiOrderedLE V] (B : Set Q)
    (Step : Q × V → Q × V → Prop) (hlap : LapNotDown B Step) (x : ℕ → Q × V)
    (hx : ∀ n, Step (x (n + 1)) (x n)) : ∀ N, ∃ n, N ≤ n ∧ (x n).1 ∈ B := by
  sorry

/-- One macro step: from a boundary configuration to the next one, through a nonempty run whose
intermediate states are off `B`. -/
def MacroStep (B : Set Q) (Step : Q × V → Q × V → Prop) (c d : Q × V) : Prop :=
  c.1 ∈ B ∧ d.1 ∈ B ∧ ∃ (x : ℕ → Q × V) (n : ℕ), 0 < n ∧ x 0 = c ∧ x n = d ∧
    (∀ i, i < n → Step (x i) (x (i + 1))) ∧ ∀ i, 0 < i → i < n → (x i).1 ∉ B

/-- **Lemma M, part 2.**  The machine is immortal iff the macro map has an infinite forward
orbit. -/
theorem immortal_iff_macro [Finite Q] [WellQuasiOrderedLE V] (B : Set Q)
    (Step : Q × V → Q × V → Prop) (hlap : LapNotUp B Step) :
    (∃ x : ℕ → Q × V, ∀ n, Step (x n) (x (n + 1))) ↔
      ∃ b : ℕ → Q × V, ∀ n, MacroStep B Step (b n) (b (n + 1)) := by
  sorry

/-- **Lemma M, part 3.**  The reverse is immortal iff the macro map has an infinite backward
chain. -/
theorem reverse_immortal_iff_macro [Finite Q] [WellQuasiOrderedLE V] (B : Set Q)
    (Step : Q × V → Q × V → Prop) (hlap : LapNotDown B Step) :
    (∃ x : ℕ → Q × V, ∀ n, Step (x (n + 1)) (x n)) ↔
      ∃ b : ℕ → Q × V, ∀ n, MacroStep B Step (b (n + 1)) (b n) := by
  sorry

end LemmaM

/-! ## 2'. Lemma M for guarded 2-counter machines -/

namespace TwoCounter

variable {Q : Type*}

/-- A guarded rule `(q, I, δ, q')`: from state `src` with counters in `guard`, add `move` and go
to `dst`. -/
structure Rule (Q : Type*) where
  /-- The state the rule leaves. -/
  src : Q
  /-- The guard on the counters. -/
  guard : Set (ℕ × ℕ)
  /-- The move added to the counters. -/
  move : ℤ × ℤ
  /-- The state the rule enters. -/
  dst : Q

/-- `ρ` fires from `c` to `c'`. -/
def Rule.Fires (ρ : Rule Q) (c c' : Q × ℕ × ℕ) : Prop :=
  c.1 = ρ.src ∧ c.2 ∈ ρ.guard ∧ c'.1 = ρ.dst ∧
    (c'.2.1 : ℤ) = c.2.1 + ρ.move.1 ∧ (c'.2.2 : ℤ) = c.2.2 + ρ.move.2

/-- One step of the machine with rule set `R` (determinism and reversibility are not needed for
Lemma M). -/
def Step (R : Set (Rule Q)) (c c' : Q × ℕ × ℕ) : Prop :=
  ∃ ρ ∈ R, ρ.Fires c c'

/-- **(S1), sharpened.**  Every closed walk `ρ 0, …, ρ (m-1)` (`m ≥ 1`) of rules of `R` whose
states are off `B` has a lap vector `∑ ρ i.move` with one negative and one positive entry.  The
paper's (S1) (each SCC off `B` trivial, or a simple cycle with one rule per edge and a mixed-sign
lap) implies this, since a closed walk there is a whole number of laps of one cycle. -/
def LapsMixed (B : Set Q) (R : Set (Rule Q)) : Prop :=
  ∀ (ρ : ℕ → Rule Q) (m : ℕ), 0 < m → (∀ i, i < m → ρ i ∈ R) →
    (∀ i, i < m → (ρ i).src ∉ B) → (∀ i, i + 1 < m → (ρ i).dst = (ρ (i + 1)).src) →
    (ρ (m - 1)).dst = (ρ 0).src →
    let δ := ∑ i ∈ Finset.range m, (ρ i).move
    (δ.1 < 0 ∧ 0 < δ.2) ∨ (δ.2 < 0 ∧ 0 < δ.1)

/-- **Lemma M for 2-counter machines.**  Under (S1), every run that is infinite forward, or
infinite backward, visits the boundary states infinitely often. -/
theorem visits_boundary [Finite Q] (B : Set Q) (R : Set (Rule Q)) (hS1 : LapsMixed B R) :
    (∀ x : ℕ → Q × ℕ × ℕ, (∀ n, Step R (x n) (x (n + 1))) →
      ∀ N, ∃ n, N ≤ n ∧ (x n).1 ∈ B) ∧
    (∀ x : ℕ → Q × ℕ × ℕ, (∀ n, Step R (x (n + 1)) (x n)) →
      ∀ N, ∃ n, N ≤ n ∧ (x n).1 ∈ B) := by
  sorry

end TwoCounter

end CollatzMoonshot.RcwaMachine
