# Handoff: amusical reversal (Lane R)

## 2026-10-13 lap: Lane R complete

The scoped objective is complete: `CollatzMoonshot/AmusicalReversal.lean` is
sorry-free, and all three ratified targets are proved without changing any
statement.

The adversarial review confirmed that the prior `ncard ≤ 2` result could not by
itself supply finite fibers (`Set.ncard` is zero on infinite sets).  The common
no-three-points argument is now factored through the actual finiteness lemma
`orbit_inter_fixedPoints_finite`; both the public cardinality theorem and the
reverse implication of `infinitelyManyOrbits_iff_reversor` use it.

For the forward implication, one point is chosen from every two-sided orbit.
Writing each point as `U^k` of its chosen base, the constructed involution sends
it to `U^(-k)` of that base.  `neg_zpow_apply_eq_of_zpow_apply_eq` proves this is
independent of the chosen exponent on finite cycles.  The map preserves sign,
reverses `amusicalPerm`, and fixes the chosen base of every nonnegative orbit;
injectivity of the base selection transfers infinitude of orbits to infinitude
of nonnegative fixed points.

Theorem NR (`no_piecewiseAffine_reversor`) is also closed.  For a bound `B` on
all products `|c_j a_k|`, choose `L = B + 1` and classify every integer by its
initial affine piece, residue modulo `4^L`, image piece after `U^L`, and the
reversor image modulo `3^L`.  Two distinct integers share one finite cell.
The exact forward/backward affine formulas then force `3^(2L)` to divide the
nonzero coefficient product `c_{j'} a_j`, contradicting
`|c_{j'} a_j| ≤ B < 3^(2L)`.

Exact verification:

```text
~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-reversal \
  --target CollatzMoonshot.AmusicalReversal \
  --axioms CollatzMoonshot.Amusical.orbit_inter_fixedPoints_ncard_le_two \
  --axioms CollatzMoonshot.Amusical.infinitelyManyOrbits_iff_reversor \
  --axioms CollatzMoonshot.Amusical.no_piecewiseAffine_reversor
```

Verdict: `FORMALIZE-TIER GREEN`.  Each headline has exactly
`[Classical.choice, Quot.sound, propext]`; the target has no declarations with
`sorry`.

Current blocker: none.  There is no further in-scope Lane R attack; do not spill
into Lane G or the separately owned amusical files.  The host can close the
scoped treadmill objective.
