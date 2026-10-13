# HANDOFF: amusical global mechanisms (2026-10-13)

## Concrete advance

- Proved `abs_le_four_pow_mul_iterate_sub` (Lemma K), forward and backward.
- Added private affine ledgers.  The forward ledger proves
  `2^B * U^[l] x = 3^l * x + c` with `l ≤ B ≤ 2l` and `|c| < 4^l` by induction;
  the backward ledger follows by applying it to `U⁻ˡ x` and cancelling the permutation powers.
- Proved `amusical_iterate_eq_add_finite` by putting every solution in the finite interval
  `[-4^l (|d|+1), 4^l (|d|+1)]`.
- The scoped file now has four remaining `sorry`s, down from six.  No statement was changed and
  no axiom or `native_decide` was added.

## Verification

Exact gate run:

```text
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-global \
  --target CollatzMoonshot.AmusicalGlobal
```

Verdict: `✅ FORMALIZE-TIER GREEN` (`lake build` completed successfully, 8715 jobs).  The only
scoped proof debt reported is the four later targets in `AmusicalGlobal.lean`; inherited sorries
in `AmusicalEscape.lean` and `AmusicalWindowThree.lean` are explicitly allowed by the kickoff.

## Current blocker

There is no external blocker.  The remaining obligations are substantial proofs:
`exists_many_returns`, `infinitelyManyOrbits_of_survival`,
`infinitelyManyOrbits_of_commuting`, and `commuting_window_two`.

## Next highest-value attack

Follow the kickoff order and prove `infinitelyManyOrbits_of_commuting` next.  Establish first that
`g` commutes with `amusicalInv` by applying `amusical_injective` to the two forward images.  Then
prove that `g '' amusicalOrbit m = amusicalOrbit (g m)` (the `amusicalPerm`/integer-power orbit
description in `AmusicalReturns.lean` may shorten this), transport `IsOrbitMin`, and show the
minima of the orbits of `g^[k] m` strictly increase.  After that, attack the finite table theorem
`commuting_window_two`, then Proposition S, and leave Proposition P for last as directed.
