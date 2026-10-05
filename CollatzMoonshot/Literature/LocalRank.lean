/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.FrontB.Dictionary

/-!
# Peer barriers on local ranking functions, as cited hypotheses

Two published barriers against a Collatz ranking function computed locally from `n`
(`RESEARCH-2026-10-05-rewriting-lane-landscape.md`).  Both are stated here as named `Prop`s,
not axioms, and both are transcribed **faithful-or-weaker**: the class of ranks excluded is a
subclass of the class the source excludes.

Transcription caveat (the step most needing an expert check): both are stated for the shortcut
map `tstep` with strict decrease at every `n > 1`.  The sources phrase termination for their own
presentation of the map (Nashida: generalized maps `(Ax+b)/2^e`; Kadirbekov: the standard map).
-/

namespace CollatzMoonshot.Literature

open Matrix
open CollatzMoonshot.FrontB (tstep)

/-- The value of a `d`-state real weighted automaton on the binary digits of `n`
(least significant digit first): `α ⬝ M_{b₀} ⬝ M_{b₁} ⋯ ⬝ β`. -/
noncomputable def automatonValue {d : ℕ} (α β : Fin d → ℝ) (M : Bool → Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) : ℝ :=
  α ⬝ᵥ (n.bits.foldr (fun b v => M b *ᵥ v) β)

/-- **Nashida, Part I** (Zenodo 10.5281/zenodo.23081447, r3 2026-10-02; the automaton-rank
barrier for entangled maps, Collatz included).  Weaker transcription: only *entrywise
positive* automata (the source also excludes finite arctic and non-negative automata with a
primitive dominant block), in every dimension `d`. -/
def NashidaPositiveAutomatonBarrier : Prop :=
  ∀ (d : ℕ) (α β : Fin d → ℝ) (M : Bool → Matrix (Fin d) (Fin d) ℝ),
    (∀ i, 0 < α i) → (∀ i, 0 < β i) → (∀ b i j, 0 < M b i j) →
      ¬ ∀ n : ℕ, 1 < n → automatonValue α β M (tstep n) < automatonValue α β M n

/-- **Kadyrbekov & Kadirbekov** (`collatz-matrix-no-go`, Zenodo 10.5281/zenodo.22098492,
`GLOBAL_ATTACK.md`): no `log₂ n + P(n)` with `P` bounded decreases at every step. -/
def KadirbekovBoundedCorrection : Prop :=
  ∀ P : ℕ → ℝ, (∃ B, ∀ n, |P n| ≤ B) →
    ¬ ∀ n : ℕ, 1 < n → Real.logb 2 ((tstep n : ℕ) : ℝ) + P (tstep n) < Real.logb 2 (n : ℝ) + P n

end CollatzMoonshot.Literature
