# HANDOFF: C1⁺ twisted Fourier inversion and frequency normalization (2026-10-26)

## Concrete advance

Added the sorry-free module `CollatzMoonshot/Conjugacy/WeakDecayTwist.lean` and imported it from
`WeakDecay.lean`, without changing any frozen statement.  It closes the exact algebraic seam left by
the preceding class/slice expansion:

- `twistedParity_eq_fourier` gives Fourier inversion of
  `(-1)^y * e(eta*2^m*y/3^(a+k))` on `ZMod (3^a)`;
- `start_phase_eq_twistedParity_mul` proves the pointwise iterate identity which factors the start
  character into that twist and the negative numerator phase;
- `sliceStartTwist_eq_fourier_twisted` is the exact per-slice Fourier expansion;
- `twoPowMulEquiv` reindexes frequencies by the unit `2^m`, eliminating the inverse of `2^m` from
  the resulting frequency;
- `twistedNumeratorSum_two_pow` and `sliceStartTwist_eq_fourier_overPrecZMod` identify every inner
  sum with the numerator character at the fine-modulus frequency `3^k*xi - eta`;
- `overPrecFrequencyNat_cast` chooses the nonnegative representative
  `3^(a+k) + 3^k*xi.val - eta.val`, and `overPrecZModSum_eq_exp_frequencyNat` renders its sum in
  exactly the exponential notation used by the frozen `overPrecChar` definition;
- `overPrecFrequencyNat_normalize` proves, for `eta != 0`, that `v = padicValNat 3 eta.val < k`,
  the representative is `3^v * overPrecFrequencyUnit ...`, and the quotient is not divisible by
  `3`.

Thus the previously conjectured valuation identity is now a kernel-checked factorization, and the
remaining Edge 1 work is analytic/asymptotic rather than modular algebra.  No new axiom,
`native_decide`, heartbeat increase, or auxiliary `sorry` was introduced.  The pre-existing
untracked `CLAUDE.local.md` remains untouched.

## Exact verification

```text
lake env lean CollatzMoonshot/Conjugacy/WeakDecayTwist.lean
  exit 0, no output

~/personal/bin/lean-green ~/src/collatz-moonshot-c1plus \
  --target CollatzMoonshot.Conjugacy.WeakDecay \
  --axioms CollatzMoonshot.Conjugacy.sliceStartTwist_eq_fourier_overPrecZMod
  Build completed successfully (8777 jobs).
  axioms: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN

~/personal/bin/lean-green ~/src/collatz-moonshot-c1plus \
  --target CollatzMoonshot.Conjugacy.WeakDecayTwist \
  --axioms CollatzMoonshot.Conjugacy.overPrecFrequencyNat_normalize
  Build completed successfully (8776 jobs).
  axioms: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN
```

The two original sorries in `WeakDecay.lean` remain, so the scoped host predicate is not yet met.

## Current blocker

The exact reduction now needs one analytic estimate for the new coefficients:

```text
sum (xi : ZMod (3^a)), norm (twistedHat m a k eta xi) <= O(a + k + 1).
```

Expanding the geometric series gives ratio
`q = -e(eta.val*2^m/3^(a+k))*stdAddChar(-xi)`.  Its numerator has norm at most `2`; its denominator
is the distance of the shifted `3^a` grid from the half-integers.  Because the shift has odd
denominator `3^(a+k)`, equality with a half-integer is impossible, and the reciprocal-distance sum
is `O(log(3^(a+k))) = O(a+k)`.  The unshifted proof from `gHatZ_closed` through
`sum_norm_gHatZ_le` in `SliceFourier.lean` supplies the template, but its denominator pairing must
be generalized to the shifted grid in this new file.

After that bound, two short exact bridges remain inside the proof of the first frozen edge:

1. use `overPrecZModSum_eq_exp_frequencyNat` to identify the inner sum with
   `overPrecChar m a k (overPrecFrequencyNat ...)`;
2. use `overPrecFrequencyNat_normalize` and cancellation of `3^v` in numerator/denominator to
   rewrite it as `overPrecChar m a (k-v) (overPrecFrequencyUnit ...)`, where `k-v >= 1` and the
   frequency is prime to `3`.

Then apply `h` at exponent `3`, `norm_sliceStartTwist_le_card` on the tails,
`outOddSet_card_mul_sq_le`, `sum_norm_gHatZ_le`'s style of Fourier-weight estimate, and C1 for the
zero mode to finish `weakDecayOnZ3_of_overPrecSliceCharDecay`.

## Next highest-value attack

Stay on Edge 1.  Prove the shifted geometric-series closed form and the `O(a+k)` l1 bound for
`twistedHat` in `WeakDecayTwist.lean`; then add the two local bridges above and assemble the first
frozen theorem.  Do not start the Sec7P padding/generalization for Edge 2 until Edge 1 is complete.
