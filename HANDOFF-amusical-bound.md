# HANDOFF: amusical word-to-lattice bridge (2026-10-13)

## Concrete advance

The existing kernel-efficient integer lattice DP and its 200-step inequality remain intact.
This lap proved the recurrence interface needed by the combinatorial bridge:

- `sum_bool_snoc` splits a sum over `(Fin (n+1) → Bool)` into the last letter and a length-`n`
  prefix via `Fin.snocEquiv`, without asking the kernel to enumerate the function space;
- `fwdLatticeStep_getD` and `bwdLatticeStep_getD` prove the exact adjacent-coordinate formula
  for a step, including the explicit left-neighbor accumulator;
- `fwdLatticeRow_succ_getD` and `bwdLatticeRow_succ_getD` lift those formulas to rows, with
  the zero boundary and final appended zero discharged;
- the backward formula visibly carries the required factor `2` for a newly marked letter.

These lemmas are kernel-checked and add no axiom, `native_decide`, or new `sorry`.

## Exact verification

```text
lake env lean CollatzMoonshot/AmusicalBound.lean
# passes; warning only at the scoped target sorry

git diff --check
# passes

~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-bound --target CollatzMoonshot.AmusicalBound
# Build completed successfully (8709 jobs); FORMALIZE-TIER GREEN
# reports exactly the scoped sorry at AmusicalBound.lean:181
```

## Current blocker

The sole remaining `sorry` is `windowDensity_two_hundred_lt`.  Its numerical content is
certified.  What remains is the semantic half of the combinatorial bridge, for every `L`:

```lean
fwdSurv L = (fwdLatticeNum L : ℚ) / 2^L
bwdSurv L = (bwdLatticeNum L : ℚ) / 3^L
```

This must connect the ratified sums over `w : Fin L → Bool` to the recurrence without asking
the kernel to enumerate function spaces.

## Next highest-value attack

Define semantic forward/backward coordinates as weighted counts of surviving words with exactly
`o` marked letters.  Apply `sum_bool_snoc`; old prefix conditions are unchanged under `Fin.snoc`,
and the sole new condition is the full-prefix guard.  Prove that these semantic coordinates obey
`fwdLatticeRow_succ_getD` / `bwdLatticeRow_succ_getD`, then identify the rows by induction and sum
over `o`.  This yields the two displayed bridge equalities.  Finally rewrite the target, clear the
positive denominators, and apply `latticeDensity_two_hundred_lt`.

Do not change `fwdSurv`, `bwdSurv`, or either ratified theorem statement.  The untracked
`CLAUDE.local.md` predates this lap and must remain uncommitted.
