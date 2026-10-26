# HANDOFF: C1⁺ / `WeakDecayOnZ3` complete (2026-10-26)

## Concrete advance

The scoped target `CollatzMoonshot/Conjugacy/WeakDecay.lean` is now sorry-free. Both frozen edge
statements and the assembled headline theorem are proved without changing any frozen statement or
editing any forbidden module.

New module `CollatzMoonshot/Conjugacy/WeakDecayTwistBound.lean` completes Edge 1:

- It identifies every shifted Fourier coefficient with a geometric sum on the fine modulus.
- Adversarial review found that the preceding handoff's claimed `O(a+k)` coefficient mass was
  false: a shifted grid point can approach the pole closely enough to cost `3^k`.
- The proved sufficient replacement is
  `sum ‖twistedHat‖ ≤ 3^k * 4 * (a+k+1)`. This is harmless because `k` is fixed.
- Frequency normalization, central-slice decay, binomial tails, the zero Fourier mode via C1, and
  finite Fourier inversion then prove `weakDecayOnZ3_of_overPrecSliceCharDecay`.

New module `CollatzMoonshot/Conjugacy/WeakDecaySec7P.lean` completes Edge 2:

- It reruns the exact Terras gap reindexing and pair-fiber cancellation with independent slice
  length `a` and character modulus `n`.
- The resulting `finePascalDamping n a` has `a/2` pair coordinates but fine-modulus pair factors.
- For `n = a+k`, it pads the missing pair sums by the fixed value `2`. Added `fPair` factors have
  norm exactly one and each padding coordinate has Pascal mass `p² ≥ 1/25`, giving the
  kernel-checked comparison `finePascalDamping ≤ 25^d * pascalDamping`,
  `d = ⌊n/2⌋-⌊a/2⌋ ≤ k`.
- The existing `TaoCollatz.Sec7P.pascal_damping_decay` supplies arbitrary polynomial decay at
  level `a+k`; the two conditioning powers are absorbed exactly as in `SliceSeven.lean`.
- This proves `overPrecSliceCharDecay`, hence `weakDecayOnZ3`.

No new axiom, `native_decide`, heartbeat increase, or auxiliary `sorry` was introduced. The
pre-existing untracked `CLAUDE.local.md` remains untouched. The frozen files
`SliceSeven/SliceFourier/C1/Recursion/Bridge3*/SliceDecay` and the read-only TaoCollatz package were
not edited.

## Exact verification

```text
lake env lean CollatzMoonshot/Conjugacy/WeakDecayTwistBound.lean
  exit 0 (style warning only)

lake env lean CollatzMoonshot/Conjugacy/WeakDecaySec7P.lean
  exit 0

lake env lean CollatzMoonshot/Conjugacy/WeakDecay.lean
  exit 0 (style warning only)

~/personal/bin/lean-green ~/src/collatz-moonshot-c1plus \
  --target CollatzMoonshot.Conjugacy.WeakDecay \
  --axioms CollatzMoonshot.Conjugacy.weakDecayOnZ3
  Build completed successfully (8779 jobs).
  CollatzMoonshot.Conjugacy.weakDecayOnZ3:
    [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN
```

Direct source scan of `WeakDecay.lean`, `WeakDecayTwistBound.lean`, and
`WeakDecaySec7P.lean` finds no `sorry`, `admit`, `axiom`, or `native_decide`.

## Current blocker

None for the scoped C1⁺ objective. The host predicate
`sorry-free:CollatzMoonshot/Conjugacy/WeakDecay.lean` is met. Unrelated pre-existing proof debt
reported by the full gate remains outside this objective.

## Next highest-value attack

Stop this treadmill campaign at the completed host gate. A future operator-directed lap may
promote `weakDecayOnZ3` into a later theorem, but should not reopen either proof or replace the
fixed-padding argument without a new objective.
