# HANDOFF: amusical global mechanisms (2026-10-14, objective complete)

## Latest lap advance

- `CollatzMoonshot/AmusicalGlobal.lean` is sorry-free. Both remaining ratified targets were
  proved without changing any statement or existing definition.
- Proposition S, `infinitelyManyOrbits_of_survival`, now transfers the exact one-sided window
  densities to the semantic survivor predicates, applies finite inclusion-exclusion, and turns
  the resulting positive density of two-sided survivors into infinitely many orbit minima.
- Proposition P, `exists_many_returns`, now factors `M = 2^a 3^b M₀`, constructs a nonempty
  return connector on `ZMod M₀`, repeats a marker word, realizes that word by an integer
  itinerary, and chooses an arbitrarily large cylinder translate by CRT. The marker prefix fixes
  the `2^a` residue, its suffix fixes the `3^b` residue, and the connector fixes the `M₀` residue.
- The connector proof formalizes the paper crux: the two odd affine branches generate the unit
  translation `z ↦ z - 2/3`. A factorial iterate represents the inverse of one branch on the
  finite ring, so the resulting semigroup reaches every residue.
- Added a local proof of finite forward-itinerary realization from
  `continuousBackwardStepWordEquiv`. This removes the initially observed inherited `sorryAx`
  from Proposition P; both new headline declarations have a clean trust ledger.

## Reflection audit

- The exact statements and definitions remained faithful to the kickoff. Proposition S's missing
  abstraction was the one-sided semantic/good-word equivalence above the existing threshold;
  Proposition P's real crux was the coprime-to-six connector, not the adic marker bookkeeping.
- The first axiom audit of Proposition P correctly exposed reliance on the inherited
  `exists_forward_itinerary` sorry. Replacing that call locally closed the dependency hole rather
  than accepting cargo-cult proof debt.
- No function type or large case space is decided, no `native_decide` is introduced, and no
  proof source outside `CollatzMoonshot/AmusicalGlobal.lean` was changed.

## Verification

Narrow checks:

```text
lake env lean CollatzMoonshot/AmusicalGlobal.lean
rg -n '\bsorry\b|sorryAx' CollatzMoonshot/AmusicalGlobal.lean
git diff --check
awk 'length($0)>100 ...' CollatzMoonshot/AmusicalGlobal.lean
```

The Lean check succeeds, the search finds no occurrence, and the diff and 100-column checks pass.

Real scoped gates:

```text
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-global \
  --target CollatzMoonshot.AmusicalGlobal \
  --axioms CollatzMoonshot.Amusical.exists_many_returns

~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-global \
  --target CollatzMoonshot.AmusicalGlobal \
  --axioms CollatzMoonshot.Amusical.infinitelyManyOrbits_of_survival
```

Both return `✅ FORMALIZE-TIER GREEN` over 8716 jobs. Each audited theorem uses exactly
`Classical.choice`, `Quot.sound`, and `propext`; neither uses `sorryAx`.

## Current blocker

None. The scoped host predicate `sorry-free:CollatzMoonshot/AmusicalGlobal.lean` is met.
Inherited proof debt in treadmill-owned `AmusicalEscape.lean` and `AmusicalWindowThree.lean`
remains out of scope and is not in either completed headline theorem's axiom ledger.

## Next highest-value attack

No further scoped attack remains. The host should accept the completed objective; any work on the
inherited files belongs to their separate treadmills.
