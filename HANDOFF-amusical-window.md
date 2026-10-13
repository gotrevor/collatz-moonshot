# HANDOFF: amusical window density (2026-10-13, affine threshold checkpoint)

## Concrete advance

The residue-class threshold step is now packaged and kernel-checked in
`CollatzMoonshot/AmusicalWindow.lean`.

- `amusicalForwardWord` and `amusicalBackwardWord` record the actual forward and backward
  branch traces, using exactly the Boolean conventions of `fwdSurv` and `bwdSurv`.
- `amusicalForwardEvenCount_eq_count` and `amusicalBackwardFourCount_eq_count` identify the
  recursive slope counters with counts along the orbit trace. These make the exponent in the
  exact affine slopes accessible to prefix-cardinality arguments.
- `amusicalForwardWord_add_pow_four_mul` proves that the length-`L` forward word is constant
  on every class modulo `4^L`.
- `amusicalBackwardWord_add_pow_three_mul` proves the analogous constancy modulo `3^L`.
- `eventually_affine_le_iff_slope_lt` proves, constructively over `ℤ`, that the eventual order
  of two affine functions with unequal integral slopes is exactly their slope order.
- `amusical_iterate_eventually_ge_iff_slope` and
  `amusicalInv_iterate_eventually_ge_iff_slope` apply that lemma to the exact forward and
  backward residue-class formulas. Thus, once slope inequality is discharged, every fixed
  residue/time comparison stabilizes beyond an explicit existential threshold. This is the
  analytic core of kickoff step 3, independent of the still-open finite counting.

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

The remaining route-decisive lemma is still the exact fiber count for the two branch-word maps over
complete residue systems: every forward word has `2^L` preimages modulo `4^L`, while a backward
word with `b` true positions has `2^b` preimages modulo `3^L`. Prefix filter-cardinalities must
also be tied to the two `Nat.count` characterizations. For the threshold lemmas just landed,
the hypotheses that the integral slopes are unequal remain to be discharged from
`3^t ≠ 2^e` (`t ≥ 1`), followed by cancellation of the common prime-power factor; then the
finitely many residue/time thresholds can be maximized. CRT product count and the
periodic-density squeeze remain downstream.

The scoped file still has its single original `sorry`, at `windowMinDensity`; the host
completion predicate is not yet met.

## Next highest-value attack

Prove the forward and backward branch-word fiber counts by induction on `L`, using the explicit
formulas in `Amusical.lean`: the forward first branch splits a class mod `4^(L+1)` into two
equipotent halves and advances to a class mod `4^L`; the backward first branch has one residue
for the divisible-by-three branch and two for the nondivisible branch. Then rewrite the prefix
cards in `fwdSurv`/`bwdSurv` through the counter lemmas. In parallel, the small slope side-goal
can be closed with the standard parity proof of `3^t ≠ 2^e` plus power cancellation, allowing
the new stabilization lemmas to be invoked without hypotheses. The fiber counts remain the
highest-value attack because they unlock the finite good-class count before CRT and asymptotics.
