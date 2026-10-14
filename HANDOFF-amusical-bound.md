# HANDOFF: amusical `1/20` density bound complete (2026-10-13)

## Concrete advance

The scoped target is complete.  A fresh review confirmed that the ratified statements still lead
from the 200-window estimate to the orbit-minimum density theorem, then closed the only missing
word-to-lattice bridge:

- `fwdLatticeCount t o` and `bwdLatticeCount t o` are semantic weighted counts of surviving
  length-`t` words with exactly `o` marked letters;
- splitting a word with `Fin.snoc` proves their adjacent-coordinate recurrences, including the
  backward factor `2` for a newly marked letter;
- induction identifies every semantic coordinate with the corresponding entry of
  `fwdLatticeRow` or `bwdLatticeRow`, and summing coordinates identifies the numerators;
- `fwdSurv_mul_two` and `bwdSurv_mul_three` establish, for every `L`,
  `2^L * fwdSurv L = fwdLatticeNum L` and
  `3^L * bwdSurv L = bwdLatticeNum L`;
- clearing the positive denominators reduces `windowDensity_two_hundred_lt` exactly to the
  existing kernel-certified `latticeDensity_two_hundred_lt`.

`CollatzMoonshot/AmusicalBound.lean` is now sorry-free.  The ratified statements and imported
definitions were unchanged; no axiom or `native_decide` was added.  Consequently the existing
`orbitMin_density_lt_one_twentieth` corollary is fully proved as well.

## Exact verification

```text
lake env lean CollatzMoonshot/AmusicalBound.lean
# passes cleanly

git diff --check
# passes

~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-bound \
  --target CollatzMoonshot.AmusicalBound \
  --axioms CollatzMoonshot.Amusical.windowDensity_two_hundred_lt
# Build completed successfully (8709 jobs); FORMALIZE-TIER GREEN
# axioms: Classical.choice, Quot.sound, propext

~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-bound \
  --axioms CollatzMoonshot.Amusical.orbitMin_density_lt_one_twentieth
# Build completed successfully (8839 jobs); FORMALIZE-TIER GREEN
# axioms: Classical.choice, Quot.sound, propext
```

## Current blocker

None for `KICKOFF-2026-10-13-amusical-bound.md` or the host predicate
`sorry-free:CollatzMoonshot/AmusicalBound.lean`.

## Next highest-value attack

Stop: the scoped objective is met, and no stretch objective was assigned.  The untracked
`CLAUDE.local.md` predates this campaign and remains deliberately uncommitted.
