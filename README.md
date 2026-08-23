# collatz-moonshot 🌙

Strategy layer for an attack on the Collatz conjecture itself - the root conjecture, not
a neighbor.  The global map lives in **[APPROACHES.md](APPROACHES.md)**; the pruned,
front-specific thread boards are **[FRONT-A-ROUTES.md](FRONT-A-ROUTES.md)** (divergence)
and **[FRONT-B-ROUTES.md](FRONT-B-ROUTES.md)** (cycles).

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
- `CollatzMoonshot/Descent.lean` - `DescentAll` ⟺ `Conjecture` (proved, strong
  induction) + `conjecture_of_fronts`, the two lane consumption forms.
- `CollatzMoonshot/FrontA/Threads.lean` - **Front A board**: finite-prefix invariance of
  divergence, divergence-only descent/frequency consumption, the fixed-seed obstruction
  to naive Tao/backward amplification, floor-preserving saturation, W1/W1′ strength pins,
  and repeat-or-descend certificates.
- `CollatzMoonshot/FrontB/` - **Front B board**: parity-word numerators, rotation
  identities, the negative-cycle falsification harness, killed routes, and the live
  bounded-circuit compression pin.
- `CollatzMoonshot/Rigidity/` - **Lane 1 (×2×3 measure rigidity)**, roadmap in
  `Rigidity.lean`.  Proved: the 2-adic extension `T2` with the base intertwining
  `T2_natCast`, and the **funnel** (`v ≡ 1 mod 4^s` crashes by `(3/4)^s` in `3s`
  steps - why cycle-charging fights divergence).  Pinned: working conjecture
  **W1** (invariant measures on a positive orbit's 2-adic closure charge the
  trivial cycle; a `def`, never an `axiom` - it's ours), and Rudolph-Johnson
  parameterized by an entropy functional (blocker: no KS entropy in mathlib).
  Furstenberg's ×2×3 topological rigidity joins the Assumed roster (1967,
  THEOREM-grade).

Private.  Substantially written by Ren (Claude); treat confidence levels as opinions.
