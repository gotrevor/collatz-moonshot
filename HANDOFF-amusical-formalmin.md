# HANDOFF: formal-minimum bookkeeping written, loader-blocked (2026-10-14)

## Concrete advance

Proofs are written for the first four targets in `AmusicalFormalMin.lean`:

- `amusicalInv_iterate_forward_iterate` cancels a bounded number of inverse iterates from a
  forward iterate, using the existing `amusicalPerm` integer-power bridge.
- `kBwd_forward_iterate` identifies the backward bit ledger at `U^[j] x` with the forward
  ledger at `x`.
- `formalMin_unique`, `not_formalMin_of_periodic`, and `formalMin_neg` use those identities.
- `infinitelyManyOrbits_of_formalMin_infinite` maps the infinite set of natural formal minima
  injectively to two-sided orbits, with injectivity supplied by `formalMin_unique`.

Reusable iterate/negation helpers are in
`CollatzMoonshot/AmusicalFormalMin/Bookkeeping.lean`, as required by the kickoff.  The ratified
definitions and theorem statements were not changed.  One `sorry` remains, exactly Proposition
G1 (`coarse_quasiInvariant_bounded`).

## Verification actually run

- `git diff --check`: PASS.
- `lake build CollatzMoonshot.AmusicalFormalMin`: loader failure while building the new helper:
  `failed to open ... .ir.sig: Too many open files`.
- `lake build CollatzMoonshot.AmusicalFormalMin.Bookkeeping`: same loader failure.
- `LEAN_NUM_THREADS=1 lake build CollatzMoonshot.AmusicalFormalMin.Bookkeeping`: same loader
  failure.  This happened before Lean emitted any source-level proof diagnostic.

The first direct `lake env lean` invocation remained alive for nearly fourteen minutes, reached
5.7 GB RSS, and was killed under the treadmill resource rule.  No green claim and no commit were
made because the new proofs have not yet been kernel-checked.

## Current blocker and next attack

The immediate blocker is environmental file-descriptor exhaustion in Lean's import loader, not a
known proof error.  On a fresh box, first build `CollatzMoonshot.AmusicalFormalMin.Bookkeeping`,
then the scoped target, and repair any ordinary elaboration errors.

After the first four targets are green, attack the sole remaining target, Proposition G1.  Its
route-decisive missing input is the paper's two-visit lemma: for fixed `M`, arbitrary residue
classes can be joined by an amusical orbit segment whose endpoints lie in one sufficiently large
dyadic block.  The theorem `amusical_no_periodic_cone` is available in
`AmusicalAntiKohl.lean`, but no such two-visit statement has yet been formalized here.
