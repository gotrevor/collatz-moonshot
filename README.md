# collatz-moonshot 🌙

Strategy layer for an attack on the Collatz conjecture itself - the root conjecture, not
a neighbor.  The map lives in **[APPROACHES.md](APPROACHES.md)**: three most-likely
routes, the three barriers any route must survive, the overlooked combinations, and the
Lean formalization program.

Siblings: [tao-collatz](https://github.com/gotrevor/tao-collatz) (formalized statistical
frontier), collatz-cryptid (cycles, carries, BB bridge - local).

## The Lean layer 🛠️

Lean 4 + mathlib (pinned v4.31.0, CoW-linked off the `~/.lake-base` universe store;
`lake build` Replays mathlib and compiles only this repo).

- `CollatzMoonshot/Basic.lean` - the map, orbit positivity, the trivial cycle.
- `CollatzMoonshot/Conjecture.lean` - `Conjecture`, the two fronts
  (`NoDivergentOrbit`, `NoNontrivialCycle`), the content-free
  `conjecture_or_not : Conjecture ∨ ¬Conjecture` smoke test, and the proved,
  axiom-free wiring theorem `conjecture_iff_split` (the conjecture ⟺ both fronts).
- `CollatzMoonshot/Assumed/` - **the axiom layer**.  This is an investigatory repo:
  believed-true unformalized results are axiomatized freely ("Assume all the
  things"), one axiom per fact, provenance in the docstring.  Doctrine and tiers in
  `Assumed.lean`; never the repo's own targets.  Current roster: Barina's `2⁶⁸`
  verification, Eliahou's cycle-length bound, Tao 2019 (proved by us in
  tao-collatz - that axiom is a citation with an upgrade path).
- `CollatzMoonshot/Conditional.lean` - first conditional results;
  `#print axioms` is the per-theorem conditionality ledger (named axioms stay
  distinguishable there, unlike `sorry`s, which all collapse into `sorryAx`).

Private.  Substantially written by Ren (Claude); treat confidence levels as opinions.
