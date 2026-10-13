# Handoff: amusical reversal (Lane R)

## 2026-10-13 lap: cyclic two-torsion leaf closed

The first of the three scoped obligations is now proved:
`orbit_inter_fixedPoints_ncard_le_two`.  No ratified statement changed.  The
proof reduces a hypothetical three distinct fixed orbit points to divisibility
of `2d` and `2e` by the orbit's `Function.minimalPeriod`.  A parity split on the
two quotient witnesses shows that the period divides `d`, `e`, or `e-d`, so
two of the three points coincide.  The infinite-set convention for `Set.ncard`
is handled explicitly by a finite/infinite split.

The bounded Aristotle job from the preceding lap was canceled after the local
proof kernel-checked:

```text
project 68ee79c1-57d5-4a35-83bb-77f20f5af53d
task    3f90e42f-392d-42e2-ac48-89bf0ed17540
```

Current blocker: two ratified proofs remain,
`infinitelyManyOrbits_iff_reversor` and `no_piecewiseAffine_reversor`.  For the
easy reversor-to-infinitely-many-orbits implication, do not use the ncard bound
alone to infer finiteness: Mathlib defines `ncard` of an infinite set as zero.
First factor the same no-three-points argument into an actual `.Finite` lemma
for each orbit/fixed-set intersection, then apply
`Set.Finite.of_finite_fibers` to the orbit map on the infinite nonnegative fixed
set.  The converse still needs the orbit-base reflection construction from the
kickoff; Theorem NR remains the final and largest obligation.

Exact verification:

```text
~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-reversal --target CollatzMoonshot.AmusicalReversal
```

Verdict: `FORMALIZE-TIER GREEN`; only the two declarations above retain
`sorry`.
