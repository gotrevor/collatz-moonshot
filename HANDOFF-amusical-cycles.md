# HANDOFF: amusical cycle structure (2026-10-14)

## Concrete advance

Two of the six scoped proof obligations in `CollatzMoonshot/AmusicalCycleBound.lean` are now
closed, with their ratified statements unchanged:

- `cycle_min_meet` identifies `V^j n` with `U^(P-j) n` on a `P`-cycle by expressing both maps as
  integer powers of `amusicalPerm`.  Forward minimality and minimal-period distinctness then give
  strict minimality in both directions, while the complementary-exponent identity gives the
  meet-in-the-middle equality when `H < P <= 2H`.
- `cycle_min_mod_six` proves that a positive cycle minimum is congruent to `2` or `4` modulo `6`.
  Odd residues contradict `n <= U n`; residue `0` contradicts `n <= V n`; both inequalities are
  obtained directly from cycle minimality, including the period-one boundary cases.

No definition, theorem statement, axiom, or computational certificate changed.  Four target
proofs remain: `amusical_cycle_min_bound`, `noNewCycles_of_search`, `cycleMinBound_31866`, and
`amusical_noNewCycles_199`.

## Exact verification

```text
lake env lean CollatzMoonshot/AmusicalCycleBound.lean
# passes (the four remaining disclosed sorries are accepted)

~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-cycles \
  --target CollatzMoonshot.AmusicalCycleBound \
  --axioms CollatzMoonshot.Amusical.cycle_min_meet
# Build completed successfully (8716 jobs); FORMALIZE-TIER GREEN
# axioms: Classical.choice, Quot.sound, propext

lake env lean CheckCycleAxioms.lean
# `#print axioms CollatzMoonshot.Amusical.cycle_min_mod_six`
# axioms: Classical.choice, Quot.sound, propext
```

## Current blocker

The route-decisive mathematical blocker is Theorem A-star, `amusical_cycle_min_bound`: formalize
the multiplicative step identity around a cycle and the product inequalities over odd steps.
The reduction theorem also needs a careful minimal-period/minimum construction, but the backward
iterate bookkeeping it consumes is now complete.

## Next highest-value attack

Introduce helper lemmas under `CollatzMoonshot/AmusicalCycleBound/` for the exact signed step
identity and its cycle product.  Work in `Rat` to cancel the positive cycle product, split the
`stepBits = 1` and `stepBits = 2` factors, and prove the two product bounds from `x_i >= m >= 1`.
Then use those inequalities to derive the stated integer `cycleMinBound` formula in
`noNewCycles_of_search`.
