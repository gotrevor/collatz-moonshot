# HANDOFF: window-3 reversors (2026-10-13)

## Concrete advance

- Proved `amusical_periodic_mem`, leaving only the final
  `no_window3_bijective_reversor` obligation in the scoped file.
- Formalized the exact affine recurrence along the actual orbit word:
  `2^B * U^p(y) = 3^p * y + N`, with `p <= B <= 2p` and
  `|N| <= 4^p - 3^p < 4^p`.
- Specialized the resulting integer inequality over the only `12 * 24` possible `(p, B)` pairs
  to obtain the safe uniform bound `|y| <= 2346`. This follows the operator's cheap route and
  does not enumerate any of the `3^p` itinerary words.
- Added a kernel check of all `y in [-2346, 2346]` and `p in [1, 12]`, which proves that every
  such periodic point has absolute value in `knownCycleMembers`.
- Proved `exists_forward_itinerary` without axioms or computation shortcuts.
- Added private cylinder lemmas showing that translation by
  `amusicalForwardPeriod t n` preserves the first `t` step symbols, and that this period is a
  power of two.
- The induction realizes a tail word first, uses coprimality of its power-of-two cylinder period
  with `3` to choose the required leading residue by CRT, then pulls the result back through the
  appropriate one of the three affine branches of `amusical`.

## Verification

- `lake env lean CollatzMoonshot/AmusicalWindowThree.lean` (passes in about 73 seconds; the sole
  warning is the one remaining target `sorry` in `no_window3_bijective_reversor`).
- `lake env lean CollatzMoonshot/AmusicalWindowThree.lean` (passes; warnings identify only the two
  remaining target sorries). [Historical verification from the preceding checkpoint.]
- `awk 'length($0) > 100 { ... }' CollatzMoonshot/AmusicalWindowThree.lean` (no output).
- `git diff --check` (passes).
- `lake env lean /tmp/AmusicalW3Audit.lean` with
  `#print axioms CollatzMoonshot.Amusical.amusical_periodic_mem` reports exactly
  `[propext, Classical.choice, Quot.sound]`.
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-w3 --target
  CollatzMoonshot.AmusicalWindowThree` (8714 jobs; final verdict `FORMALIZE-TIER GREEN`; the target
  file has exactly the one remaining `sorry` named below).

## Current blocker

The scoped file has one obligation left: `no_window3_bijective_reversor`. It depends on
encoding/checking the finite partial-rule and orphan certificates. There is no external blocker.

## Next highest-value attack

Formalize the 24 partial rules and 216 orphan certificates, then combine them with
`exists_forward_itinerary`. A tractable finite interface should parameterize a cycle assignment
by the images of the nine cycle representatives, each restricted to the subtype of points having
the matching exact period; this leaves about 2.5 million raw assignments rather than quantifying
over arbitrary functions on all 41 signed cycle points. Reconstruct each cycle image by backward
iteration, kernel-check that window/output consistency yields one of the 24 partial rules, and
kernel-check the nine completions of each rule against the supplied orphan list. In the bridge,
`amusical_periodic_mem` restricts every cycle-point image to the signed known-cycle set, while
injectivity preserves exact period.
