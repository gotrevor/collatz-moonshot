# HANDOFF: amusical global mechanisms (2026-10-14, survival semantics)

## Concrete advance

- Kernel-checked Proposition S's orbit-theoretic core: `isOrbitMin_iff_survivors` proves that
  surviving forever in both directions is exactly `IsOrbitMin`.
- Added explicit finite forward/backward window predicates, proved their conjunction is exactly
  `IsWindowMin`, and proved infinite-horizon survivors imply their corresponding finite window
  predicates. The remaining Proposition S work is now a finite-cardinality density estimate.
- Proved `commuting_window_two` with its ratified statement unchanged.
- Added `CollatzMoonshot/AmusicalGlobal/WindowTwo.lean`, whose finite certificate uses the
  cycles through `44` and `-44` to classify the two-symbol table. The certificate ranges only
  over indexed cycle data; it never quantifies over `Fin 3 → Fin 3 → Fin 3`.
- Removed the failed all-function `decide +kernel` route recorded in the kickoff. In particular,
  no proof enumerates the `3^9` function space.
- Avoided inherited proof debt from `amusical_periodic_mem`: the existing affine ledger gives
  `7153 * |y| < 4^12` for a point fixed by `U^12`, hence `|y| ≤ 2345`. A kernel check over
  `Fin 2346` classifies the nonnegative possibilities, and oddness supplies the signed list.
- The `44` and `-44` itinerary words reduce every compatible table to exactly the seven
  constant, signed-projection, and signed-successor tables. Forward-itinerary extensionality
  then identifies `g` with `0`, `1`, `-1`, `id`, `-id`, `U`, or `-U`.
- The scoped file has two remaining `sorry`s. No axiom, `native_decide`,
  statement change, or change to an existing definition was introduced.

## Verification

Exact gate run:

```text
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-global \
  --target CollatzMoonshot.AmusicalGlobal \
  --axioms CollatzMoonshot.Amusical.commuting_window_two
```

Verdict: `✅ FORMALIZE-TIER GREEN` (`lake build` completed successfully, 8716 jobs).
`commuting_window_two` has exactly the trust-base axioms `Classical.choice`, `Quot.sound`, and
`propext`; in particular, it has no `sorryAx`. The only scoped proof debt is now
`exists_many_returns` and `infinitelyManyOrbits_of_survival`.

The same exact gate was rerun after adding the survival semantics and again returned
`✅ FORMALIZE-TIER GREEN` (8716 jobs).

Additional narrow checks run:

```text
lake build CollatzMoonshot.AmusicalGlobal.WindowTwo
lake env lean CollatzMoonshot/AmusicalGlobal.lean
python3 scripts/amusical/central_w2.py
git diff --check
```

All passed. Both edited Lean files also pass the kickoff's 100-character line limit.

## Current blocker

There is no external blocker. Proposition S and Proposition P remain substantial formal proofs.
The host predicate is not yet met because those two declarations still contain `sorry`.

## Next highest-value attack

Finish `infinitelyManyOrbits_of_survival`. Prove density lemmas for the two finite halves using
`count_fwdGood`, `count_bwdGood`, `fwdSurv_mul`, and `bwdSurv_mul`, then combine their cardinals
with `windowMinDensity` through `|F ∪ B| = |F| + |B| - |F ∩ B|`. Inclusion-exclusion and
`isOrbitMin_iff_survivors` then give infinitely many minima. After Proposition S, attack
`exists_many_returns` last.
