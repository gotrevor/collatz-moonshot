/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.RcwaOrbitCount

/-!
# Totality family, layer 1: an increment chain glued into a machine

The totality family `e ↦ F e` of `RcwaOrbitCount.TotalityFamily` is one fixed machine plus an
`e`-dependent chain of increments.  This file is the generic gluing layer (research note
`undec-lemma` §7-§8; kickoff `KICKOFF-2026-10-16-totality.md`).

1. **The chain.**  For a counter machine `U` on states `Q`, a state `hole` that no rule leaves and
   a state `back` that no rule enters, `glue U hole back i L` is `U` on the states `Q ⊕ Fin L`
   together with the chain `hole → 0 → 1 → ⋯ → L − 1 → back`, each link an increment of counter
   `i` (`L + 1` increments in all).  So a pass through the chain adds `L + 1` to counter `i`.
2. **Gluing commutes with the history wrapper**, for everything the compile needs.  The chain is
   glued *after* wrapping, at the boundary states `bnd hole → … → bnd back`, so it is not
   history-wrapped and the wrapper's labels stay those of the fixed `U`:
   * the glued wrapper is deterministic and reversible (`glueH_det`, `glueH_rev`);
   * its reverse is mortal (`glueH_revMortal`): the potential `(L + 2) · hist + position` rises
     along every boundary-to-boundary macro step (a wrapper macro step raises `hist`, a chain step
     raises the position);
   * it is mortal iff the glued `U` is (`glueH_mortal_iff`): Lemma M forward for garbage, and the
     history simulation for the converse.

So the `e`-dependence never passes through `histWrap`; `RcwaTotalityCompile` handles `godel` and
`double`.
-/

namespace CollatzMoonshot.CounterMachine

/-- Relabel the states of a quadruple. -/
def Quad.mapQ {Q Q' ι : Type*} (f : Q → Q') (ρ : Quad Q ι) : Quad Q' ι :=
  ⟨f ρ.src, ρ.op, f ρ.dst⟩

/-- Relabel the states of a machine: the images of its rules. -/
def CM.mapQ {Q Q' ι : Type*} (f : Q → Q') (M : CM Q ι) : CM Q' ι :=
  {ρ' | ∃ ρ ∈ M, ρ' = ρ.mapQ f}

end CollatzMoonshot.CounterMachine

namespace CollatzMoonshot.RcwaTotality

open CollatzMoonshot.CounterMachine CollatzMoonshot.RcwaHalting
open CollatzMoonshot.RcwaOrbitCount (Mortal)

/-! ## 1. The chain -/

section Glue

variable {Q ι : Type*}

/-- The first chain state: `0`, or `back` when the chain is empty. -/
def chainFirst (back : Q) (L : ℕ) : Q ⊕ Fin L :=
  if h : 0 < L then .inr ⟨0, h⟩ else .inl back

/-- The successor of chain state `k`: `k + 1`, or `back` after the last. -/
def chainNext (back : Q) {L : ℕ} (k : Fin L) : Q ⊕ Fin L :=
  if h : k.val + 1 < L then .inr ⟨k.val + 1, h⟩ else .inl back

/-- The chain `hole → 0 → ⋯ → L − 1 → back`, `L + 1` increments of counter `i`. -/
def chain (hole back : Q) (i : ι) (L : ℕ) : CM (Q ⊕ Fin L) ι :=
  {ρ | ρ = ⟨.inl hole, .inc i, chainFirst back L⟩ ∨
    ∃ k : Fin L, ρ = ⟨.inr k, .inc i, chainNext back k⟩}

/-- `U` with the chain glued from `hole` to `back`. -/
def glue (U : CM Q ι) (hole back : Q) (i : ι) (L : ℕ) : CM (Q ⊕ Fin L) ι :=
  U.mapQ Sum.inl ∪ chain hole back i L

variable {U : CM Q ι} {hole back : Q} {i : ι} {L : ℕ}

/-- A step of `U` is a step of the glued machine. -/
theorem glue_step_inl {q q' : Q} {v v' : ι → ℕ} (h : U.Step (q, v) (q', v')) :
    (glue U hole back i L).Step (.inl q, v) (.inl q', v') := by
  sorry

/-- Off `hole`, a step of the glued machine from a state of `U` is a step of `U`. -/
theorem glue_step_inl_inv {q : Q} {v : ι → ℕ} {d : Cfg (Q ⊕ Fin L) ι} (hq : q ≠ hole)
    (h : (glue U hole back i L).Step (.inl q, v) d) :
    ∃ q', d.1 = .inl q' ∧ U.Step (q, v) (q', d.2) := by
  sorry

/-- **The chain adds `L + 1`.**  From `hole` the glued machine reaches `back` with `L + 1` added
to counter `i`. -/
theorem glue_chain_reaches [DecidableEq ι] (v : ι → ℕ) :
    Relation.TransGen (glue U hole back i L).Step (.inl hole, v)
      (.inl back, Function.update v i (v i + (L + 1))) := by
  sorry

/-- From chain state `k` the glued machine reaches `back` with `L − k` added to counter `i`. -/
theorem glue_chain_reaches_of_inr [DecidableEq ι] (k : Fin L) (v : ι → ℕ) :
    Relation.TransGen (glue U hole back i L).Step (.inr k, v)
      (.inl back, Function.update v i (v i + (L - k.val))) := by
  sorry

/-- No configuration on the chain (`hole` included) is a halting ID. -/
theorem glue_not_stuck_chain {q : Q ⊕ Fin L} (hq : q = .inl hole ∨ ∃ k : Fin L, q = .inr k)
    (v : ι → ℕ) : ¬ (glue U hole back i L).Stuck (q, v) := by
  sorry

/-- **Gluing keeps determinism** when no rule of `U` leaves `hole`. -/
theorem glue_det (hU : U.Det) (hhole : ∀ ρ ∈ U, ρ.src ≠ hole) :
    (glue U hole back i L).Det := by
  sorry

/-- **Gluing keeps reversibility** when no rule of `U` enters `back`. -/
theorem glue_rev (hU : U.Rev) (hback : U.NormalAt back) : (glue U hole back i L).Rev := by
  sorry

/-- (S1) passes to the glued machine, with the chain states and the boundary of `U` as
boundary. -/
theorem glue_lapsMixed [DecidableEq ι] {B : Set Q} (h : LapsMixed U B) (hhole : hole ∈ B) :
    LapsMixed (glue U hole back i L) (Sum.inl '' B ∪ Set.range Sum.inr) := by
  sorry

/-- **Macro steps of the glued machine.**  A boundary-to-boundary macro step is a macro step of
`U` (on states of `U`) or a single chain step. -/
theorem glue_macroStep_cases {B : Set Q} (hhole : hole ∈ B) (hback : back ∈ B)
    {b b' : Cfg (Q ⊕ Fin L) ι}
    (hm : RcwaMachine.MacroStep (Sum.inl '' B ∪ Set.range Sum.inr)
      (glue U hole back i L).Step b b') :
    (∃ c c' : Cfg Q ι, b = (.inl c.1, c.2) ∧ b' = (.inl c'.1, c'.2) ∧
      RcwaMachine.MacroStep B U.Step c c') ∨ (chain hole back i L).Step b b' := by
  sorry

end Glue

/-! ## 2. Gluing after the history wrapper -/

section GlueHist

variable {Q ι : Type*} {K : ℕ} {U : CM Q ι} {lab : Quad Q ι → Fin K} {hole back : Q} {i : ι}
  {L : ℕ}

/-- No rule of the wrapper leaves `bnd hole` when no rule of `U` leaves `hole`. -/
theorem histWrap_src_ne_bnd (hhole : ∀ ρ ∈ U, ρ.src ≠ hole) :
    ∀ r ∈ histWrap U lab, r.src ≠ .bnd hole := by
  sorry

/-- The glued wrapper is deterministic. -/
theorem glueH_det (hU : U.Det) (hhole : ∀ ρ ∈ U, ρ.src ≠ hole) :
    (glue (histWrap U lab) (.bnd hole) (.bnd back) (.val i) L).Det :=
  glue_det (histWrap_det hU) (histWrap_src_ne_bnd hhole)

/-- The glued wrapper is reversible. -/
theorem glueH_rev (hU : U.Det) (hlab : ∀ ρ ∈ U, 1 ≤ (lab ρ).val)
    (hinj : ∀ ρ ∈ U, ∀ ρ' ∈ U, lab ρ = lab ρ' → ρ = ρ') (hback : U.NormalAt back) :
    (glue (histWrap U lab) (.bnd hole) (.bnd back) (.val i) L).Rev :=
  glue_rev (histWrap_rev hU hlab hinj) (histWrap_normalAt hback)

/-- **The glued wrapper has a mortal reverse.**  Along every boundary macro step the potential
`(L + 2) · hist + pos` rises (`pos` is `0` at `bnd hole`, `k + 1` at chain state `k`, `L + 1` at
every other `bnd s`): a wrapper macro step raises `hist` (`histWrap_macro_hist`), a chain step
keeps `hist` and raises `pos`. -/
theorem glueH_revMortal [Fintype Q] [Fintype ι] [DecidableEq Q] [DecidableEq ι] (hU : U.Det)
    (hlab : ∀ ρ ∈ U, 1 ≤ (lab ρ).val) (hhb : hole ≠ back) :
    (glue (histWrap U lab) (.bnd hole) (.bnd back) (.val i) L).RevMortal := by
  sorry

/-- **Mortality through the glued wrapper.**  The glued wrapper halts from every configuration
iff the glued `U` does. -/
theorem glueH_mortal_iff [Fintype Q] [Fintype ι] [DecidableEq ι] (hU : U.Det)
    (hhole : ∀ ρ ∈ U, ρ.src ≠ hole) :
    Mortal (glue (histWrap U lab) (.bnd hole) (.bnd back) (.val i) L) ↔
      Mortal (glue U hole back i L) := by
  sorry

end GlueHist

end CollatzMoonshot.RcwaTotality
