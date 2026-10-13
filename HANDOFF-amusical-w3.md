# HANDOFF: window-3 reversors (2026-10-13)

## Concrete advance

- Proved `exists_forward_itinerary` without axioms or computation shortcuts.
- Added private cylinder lemmas showing that translation by
  `amusicalForwardPeriod t n` preserves the first `t` step symbols, and that this period is a
  power of two.
- The induction realizes a tail word first, uses coprimality of its power-of-two cylinder period
  with `3` to choose the required leading residue by CRT, then pulls the result back through the
  appropriate one of the three affine branches of `amusical`.

## Verification

- `lake env lean CollatzMoonshot/AmusicalWindowThree.lean` (passes; warnings identify only the two
  remaining target sorries).
- `awk 'length($0) > 100 { ... }' CollatzMoonshot/AmusicalWindowThree.lean` (no output).
- `git diff --check` (passes).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-w3 --target
  CollatzMoonshot.AmusicalWindowThree` (8714 jobs; final verdict `FORMALIZE-TIER GREEN`; the target
  file has exactly the two remaining sorries named below).

## Current blocker

The scoped file has two obligations left: `amusical_periodic_mem` and the final
`no_window3_bijective_reversor`. The final theorem depends on the periodic classification and on
encoding/checking the finite partial-rule and orphan certificates. There is no external blocker.

## Next highest-value attack

Prove `amusical_periodic_mem`. Derive a uniform explicit bound for a point of period `p <= 12`
from the affine branch recurrence (the supplied independent calculation gives `|y| <= 483`), then
kernel-check the bounded range for each `p`. Once that lemma is closed, formalize the 24 partial
rules and 216 orphan certificates and combine them with `exists_forward_itinerary`.
