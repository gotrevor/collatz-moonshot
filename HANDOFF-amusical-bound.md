# HANDOFF: amusical 200-step lattice certificate (2026-10-13)

## Concrete advance

`CollatzMoonshot/AmusicalBound.lean` now contains a kernel-efficient integer lattice DP:

- `fwdLatticeRow` stores counts of surviving forward prefixes by number of marked letters;
- `bwdLatticeRow` stores backward weight numerators, using transition weights `1` and `2`;
- both row lengths are proved to be `t + 1`;
- `latticeDensity_values` reproduces the ratified densities for `L = 1,2,3,4` using
  `decide +kernel`;
- `latticeDensity_two_hundred_lt` proves
  `20 * fwdLatticeNum 200 * bwdLatticeNum 200 < 2^200 * 3^200` using
  `decide +kernel`.  The cold file check took about 29 seconds, and a warm repeat about 9
  seconds.  No `native_decide`, axiom, or extra `sorry` was added.

The step functions pass the previous coordinate explicitly.  This is important: it makes
kernel reduction of each row linear instead of recomputing a recursive preceding row for every
coordinate.

## Exact verification

```text
lake env lean CollatzMoonshot/AmusicalBound.lean
# passes; warning only at the pre-existing target sorry

git diff --check
# passes

~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-bound \
  --target CollatzMoonshot.AmusicalBound
# Build completed successfully (8709 jobs); FORMALIZE-TIER GREEN
# reports exactly the pre-existing sorry at AmusicalBound.lean:92
```

## Current blocker

The sole remaining `sorry` is still `windowDensity_two_hundred_lt`.  Its numerical content is
now certified.  What remains is the combinatorial bridge, for every `L`:

```lean
fwdSurv L = (fwdLatticeNum L : ℚ) / 2^L
bwdSurv L = (bwdLatticeNum L : ℚ) / 3^L
```

This must connect the ratified sums over `w : Fin L → Bool` to the recurrence without asking
the kernel to enumerate function spaces.

## Next highest-value attack

Prove a generic one-letter extension lemma using `Fin.consEquiv`, as recommended by
`reference/lean-decide-stuck-on-pi-fintype.md`.  Organize surviving words by their mark count and
induct on `L`; the new full-prefix condition is exactly the guard in `fwdLatticeStep` or
`bwdLatticeStep`.  First prove the coordinate invariant for `List.getD`; summing it yields the two
displayed bridge equalities.  Then rewrite the target, clear the positive denominators, and apply
`latticeDensity_two_hundred_lt`.

Do not change `fwdSurv`, `bwdSurv`, or either ratified theorem statement.  The untracked
`CLAUDE.local.md` predates this lap and must remain uncommitted.
