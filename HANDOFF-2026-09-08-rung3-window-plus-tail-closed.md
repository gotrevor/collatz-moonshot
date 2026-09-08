# Handoff: rung 3 window and exceptional tail closed

**Date**: 2026-09-08 · **Branch**: `main` · nothing pushed — host pushes.

## Objective and result

The `KICKOFF-2026-09-07-rung3.md` window-node target is complete.  This review lap also closes
the statement-level tail between the already-landed window theorem and the kickoff's advertised
classification:

- `FrontA.threeBlock_window_infeasible`, `FrontA.threeBlock_gap_of_long`, and
  `FrontA.threeBlock_not_acyclicParadoxical_of_long` exclude every length outside
  `{5,8,16,27}`;
- `FrontA.threeBlock_not_acyclicParadoxical_of_exceptional` excludes the exceptional lengths
  `5`, `16`, and `27`;
- `FrontA.threeBlock_length_eq_eight_of_acyclicParadoxical` proves that a front-normalized
  three-odd-block acyclic paradoxical segment has length exactly `8`;
- `scripts/check-proof-debt.sh` reports zero disclosed sorries.

This is a classification of segments satisfying the displayed front-normalized word equation
`[T]^b[F]^c[T]^d[F]^e[T]^f[F]^g`, with the five block-positivity hypotheses in the theorem.  It
does not prove Collatz, either global front, or an unqualified claim about every arbitrary word.

## Adversarial review finding

The pre-lap source was internally sound but its headline route was incomplete.  The theorem
`threeBlock_not_acyclicParadoxical_of_long` only ruled out lengths outside `{5,8,16,27}`; it
could not by itself imply literal length `8`.  The newest handoff and `PENDING_WORK.md` disclosed
this accurately, while the one-lap-stale `DIRECTION.md` still said “hence.”  This lap attacked
that load-bearing finite tail instead of merely relabeling the existing theorem.

## Concrete advance

1. Added nested natural ceiling scales `threeBlock_minW₂` and `threeBlock_minW₁`, then proved
   `threeBlock_minW₁_le`: every actual integer cascade lies above that head scale.
2. Added `threeBlock_exceptional_residue_cert`, one `decide +kernel` theorem over the three
   exceptional lengths.  The ceiling criterion prunes the search to ten tuples.  For each, the
   theorem checks a complete parity trace, the canonical residue above `2`, and failure of the
   exact acyclic inequality.  The ten least starts are
   `33, 63759, 41679, 18783, 60255, 64351, 80553407, 50946431, 110715135, 120086783`.
3. Proved `canonicalResidueAboveTwo_le`: the canonical representative strictly above `2` is no
   larger than any other natural in the same residue class that is strictly above `2`.
4. Used `traceWord_eq_imp_modEq` to transfer each certified rejection from the least start to an
   arbitrary start realizing the same word, yielding the exceptional theorem and final
   length-8 classification.
5. Extended `scripts/AxiomAudit.lean` and reconciled `README.md`, `PENDING_WORK.md`, `STATUS.md`,
   and the source prose with the theorem actually checked by Lean.

## Verification actually run

- `python3 experiments/rung3_census.py verify` — reproduced all ten rejected exceptional starts
  and the four genuine length-8 witnesses.
- `taskset -c 0-3 lake build CollatzMoonshot.FrontA.ThreeBlock` — green (8730 jobs; 99s).
- `taskset -c 0-3 lake env lean scripts/AxiomAudit.lean` — green after adding the exceptional and
  final classification theorems.
- `taskset -c 0-3 lake build` — green after the final source and documentation consolidation.
- `bash scripts/check-proof-debt.sh` — `0 disclosed sorries`.
- `git diff --check` — clean.

## Trust ledger

There is no `sorryAx` and no new literature axiom.  The new finite certificate uses
`decide +kernel`, not `native_decide`.  The axiom audit prints only
`[propext, Classical.choice, Quot.sound]` for
`threeBlock_not_acyclicParadoxical_of_exceptional`.  The final classification theorem inherits
the pre-existing Rhin-lite/window native certificates through its long-length branch, including
the disclosed large power comparison and pruned residual census; the exceptional branch adds no
native artifact.

## Current blocker and next attack

There is no blocker or remaining obligation for the assigned rung-3 window-node objective.
`DIRECTION.md` is intentionally not edited because it is altitude-owned and one lap stale; the
next lap should await a fresh operator retarget.  A separate possible strengthening is an exact
classification of the surviving length-8 block tuples, but that is outside this kickoff.
