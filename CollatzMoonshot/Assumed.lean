/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Assumed.Computation
import CollatzMoonshot.Assumed.Cycles
import CollatzMoonshot.Assumed.Tao2019
import CollatzMoonshot.Assumed.Furstenberg
import CollatzMoonshot.Assumed.ABC

/-!
# Assumed - the axiom layer 🧨

**This repo's axiom policy is deliberately permissive** (Trevor, 2026-07-20:
"Assume all the things!").  This is an *investigatory* repo: the point is to see
the shape of the territory, and refusing to stand on known results until each is
formalized would be walking to base camp.  Unlike the gallery/expedition repos,
axioms here are a feature, not a smell.

## The three tiers

* **THEOREM-grade** (default): published, peer-reviewed proofs not yet formalized,
  and massive replicated computations.  Examples here: Eliahou's cycle bound,
  Barina's `2⁶⁸` verification, Tao 2019 (which we in fact formalized -
  its axiom is a citation with an upgrade path).
* **CONJECTURE-grade** (allowed, labeled): open statements the community broadly
  believes (abc, Furstenberg-stiffness, ...).  Anything built on one is honestly
  conditional - say so in the docstring.  (collatz-cryptid's `Axioms.lean` has
  precedent: abc/Pillai/Catalan, per the same directive.)
* **NEVER**: this repo's own targets - `Conjecture`, `NoDivergentOrbit`,
  `NoNontrivialCycle` - or anything trivially equivalent to them.  Assuming the
  target proves nothing and poisons every `#print axioms` downstream.

## The ledger

`#print axioms <thm>` is the automatic conditionality ledger: it names exactly
which assumptions a result stands on.  This is why the layer uses **axioms, not
`sorry`s**: named axioms stay distinguishable in the footprint, while every
`sorry` in a development collapses into the single anonymous `sorryAx` - a ledger
that can't tell you *which* debt you took on.  Keep one axiom per believed fact,
docstring'd with provenance, and the ledger stays legible.
-/
