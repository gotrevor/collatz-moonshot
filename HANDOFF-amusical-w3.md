# HANDOFF: window-3 reversors (2026-10-13)

## Update 2026-10-14: exact-period cycle transport proved

- Added both iterate directions of the reversor identity:
  `reversor_iterate_forward` and `reversor_iterate_backward`.
- Defined `HasExactAmusicalPeriod` and proved `reversor_preserves_exact_period`: injective
  reversors preserve the least positive period, not merely periodicity.
- Combined that result with `amusical_periodic_mem` in
  `reversor_image_mem_exactPeriodCandidates`.  Thus every source representative of period
  `p <= 12` maps to a signed known-cycle point of exact period `p`.  This supplies the missing
  dynamical-to-finite interface needed to parameterize the final check by the four independent
  cycle-length groups (`6 * 8 * 50 * 288` assignments), rather than arbitrary integer images.

Verification:

- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-w3 --target
  CollatzMoonshot.AmusicalWindowThree` passes (8714 jobs; `FORMALIZE-TIER GREEN`).
- `awk 'length($0) > 100 { print NR ":" length($0) ":" $0 }'
  CollatzMoonshot/AmusicalWindowThree.lean` has no output.
- `git diff --check` passes.

Current blocker: the sole scoped `sorry` remains `no_window3_bijective_reversor`.  It is now a
finite certificate integration problem: encode the period-preserving cycle assignments, prove
their 25 forced window values are one of the 24 supplied partial rules, and check the nine
completions of each rule against its supplied orphan.

Next attack: define compact assignment codes `Fin 6`, `Fin 8`, `Fin 50`, and `Fin 288` for the
period `1`, `2`, `5`, and `12` cycle groups.  Reconstruct all cycle images with
`reversor_iterate_forward`, kernel-check the 24-rule/orphan table, then invoke
`orphan_forbids_surjective_reversor`.

## Update 2026-10-14: orphan-to-surjectivity bridge proved

- Added the decidable `IsWindowThreeOrphan` predicate with exactly the certificate convention in
  `scripts/amusical/w3certs.txt`.
- Proved `orphan_forbids_surjective_reversor`: for any local rule `f`, a finite orphan rules out a
  surjective reversor.  The proof realizes the orphan word using `exists_forward_itinerary`, pulls
  a preimage back by surjectivity, and proves by reversor algebra that its forward output word is
  `f (s (j+2)) (s (j+1)) (s j)`, contradicting the orphan.
- This closes the entire infinite argument after the finite certificate.  The only remaining
  obligation is now finite: show that cycle consistency puts `f` among the 24 partial rules and
  kernel-check the supplied orphan for each of their nine completions.

Verification:

- `lake env lean CollatzMoonshot/AmusicalWindowThree.lean` passes (only the intended final target
  `sorry` remains; about 63 seconds).
- `awk 'length($0) > 100 { ... }' CollatzMoonshot/AmusicalWindowThree.lean` has no output.
- `git diff --check` passes.
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-w3 --target
  CollatzMoonshot.AmusicalWindowThree` passes (8714 jobs; `FORMALIZE-TIER GREEN`).  An initial
  attempt hit a transient `Too many open files` while opening a cached mathlib object; the clean
  retry is the recorded verdict.

Next attack: encode the nine cycle representatives by period-preserving permutations and phases
(only `6 * 8 * 50 * 288 = 691200` assignments), check consistency gives one of the 24 partial
rules, and encode/check the 216 listed orphan witnesses.  Then invoke
`orphan_forbids_surjective_reversor` to close the headline theorem.

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
