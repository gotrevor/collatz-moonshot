# HANDOFF: amusical window density (2026-10-13)

## Concrete advance

The branch-word bridge identified by the preceding handoff is now partly kernel-checked in
`CollatzMoonshot/AmusicalWindow.lean`.

- `amusicalForwardWord` and `amusicalBackwardWord` record the actual forward and backward
  branch traces, using exactly the Boolean conventions of `fwdSurv` and `bwdSurv`.
- `amusicalForwardEvenCount_eq_count` and `amusicalBackwardFourCount_eq_count` identify the
  recursive slope counters with counts along the orbit trace. These make the exponent in the
  exact affine slopes accessible to prefix-cardinality arguments.
- `amusicalForwardWord_add_pow_four_mul` proves that the length-`L` forward word is constant
  on every class modulo `4^L`.
- `amusicalBackwardWord_add_pow_three_mul` proves the analogous constancy modulo `3^L`.

Thus both residue-dependence assertions in kickoff steps 1 and 2 are now explicit statements,
not only consequences left implicit in the affine formulas. No ratified definition or target
was changed, and no new axiom, certificate, `sorry`, or heartbeat override was added.

One Aristotle project was submitted for the complete target while this work proceeded:
`e94297bf-c4a8-41e0-bff8-722bef5437c0`. It was still `RUNNING` at checkpoint time. A later lap
may inspect and kernel-check it, but should not trust or wait on it instead of advancing the
proof.

## Exact verification

```text
lake env lean CollatzMoonshot/AmusicalWindow.lean
git diff --check
~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-window \
  --target CollatzMoonshot.AmusicalWindow
```

Verdict: `FORMALIZE-TIER GREEN` (8707 jobs). The gate reports exactly the one pre-existing
proof debt, `windowMinDensity`.

## Current blocker

The remaining route-decisive lemma is the exact fiber count for the two branch-word maps over
complete residue systems: every forward word has `2^L` preimages modulo `4^L`, while a backward
word with `b` true positions has `2^b` preimages modulo `3^L`. Prefix filter-cardinalities must
also be tied to the two new `Nat.count` characterizations. Threshold comparison, CRT product
count, and periodic-density squeeze remain downstream.

The scoped file still has its single original `sorry`, at `windowMinDensity`; the host
completion predicate is not yet met.

## Next highest-value attack

Prove the forward and backward branch-word fiber counts by induction on `L`, using the explicit
formulas in `Amusical.lean`: the forward first branch splits a class mod `4^(L+1)` into two
equipotent halves and advances to a class mod `4^L`; the backward first branch has one residue
for the divisible-by-three branch and two for the nondivisible branch. Then rewrite the prefix
cards in `fwdSurv`/`bwdSurv` through the new counter lemmas. This directly unlocks the finite
good-class count before CRT and asymptotics.
