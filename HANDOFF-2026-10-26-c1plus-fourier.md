# HANDOFF: C1⁺ exact class Fourier reduction (2026-10-26)

## Concrete advance

Added the sorry-free module `CollatzMoonshot/Conjugacy/WeakDecayAux.lean` and imported it from
`WeakDecay.lean`.  It proves the exact finite algebra at the front of Edge 1 without changing any
frozen statement:

- `zmod_class_indicator`: normalized additive-character orthogonality is the indicator of one
  class in `ZMod M`;
- `biasClassPow_cast_eq_fourier`: every canonical class `c < 3^k` is the inverse Fourier transform
  of the signed start transforms `startTwist`;
- `biasClassPow_eq_zero_of_pow_le`: noncanonical labels `c >= 3^k` select no starts;
- `startTwist_eq_sum_sliceStartTwist` and
  `biasClassPow_cast_eq_fourier_slices`: the transform is exactly partitioned into the `m+1`
  odd-count slices;
- `startTwist_zero` and `sliceStartTwist_zero`: the zero modes are `bias` and `levelSign`;
- `norm_sliceStartTwist_le_card`: the tail slices have the needed elementary cardinality bound;
- `three_pow_mul_le_two_pow_iterate` and `iterateNumerator_eq_numer`: on a slice, the natural
  subtraction in `overPrecChar` is exact and equals `numer (traceWord r m)`.

No new axiom, `native_decide`, heartbeat increase, or auxiliary `sorry` was introduced.  The
untracked pre-existing `CLAUDE.local.md` was left untouched.

## Exact verification

```text
lake build CollatzMoonshot.Conjugacy.WeakDecayAux
  Build completed successfully (8775 jobs).

~/personal/bin/lean-green ~/src/collatz-moonshot-c1plus \
  --target CollatzMoonshot.Conjugacy.WeakDecay \
  --axioms CollatzMoonshot.Conjugacy.biasClassPow_cast_eq_fourier_slices
  Build completed successfully (8776 jobs).
  axioms: [Classical.choice, Quot.sound, propext]
  FORMALIZE-TIER GREEN
```

The two original sorries in `WeakDecay.lean` remain; the scoped host predicate is not yet met.

## Current blocker

The next exact seam in Edge 1 is not asymptotic: prove a Fourier inversion formula for each
`sliceStartTwist m a k eta`.  With `y = tstep^[m] r` and
`N = 2^m*y - 3^a*r`, rewrite

```text
e(eta*r/3^k) = e(eta*2^m*y/3^(a+k)) * e(-eta*N/3^(a+k)).
```

Fourier-expand the first factor as a function of `y : ZMod (3^a)`.  After replacing
`y` by `2^(-m) N (mod 3^a)`, the resulting frequency is
`zeta = 3^k*xi*2^(-m) - eta`.  The proof should be carried out in `WeakDecayAux.lean`, preferably
with a raw `ZMod` character definition whose final exponential form is definitionally connected
to the frozen `overPrecChar` in the proof of the edge.

The number-theoretic normalization after that is the decisive small lemma: if `eta != 0` and
`v = v3(eta) < k`, then every such `zeta` has exactly valuation `v`; divide numerator and
denominator by `3^v` to obtain an `overPrecChar m a (k-v)` at a unit frequency.  Once this exact
formula exists, reuse `sum_norm_gHatZ_le`'s `O(a)` Fourier-weight proof, the new tail bound above,
`outOddSet_card_mul_sq_le`, and `h : OverPrecSliceCharDecay` with exponent `3` to finish
`weakDecayOnZ3_of_overPrecSliceCharDecay`.

## Next highest-value attack

Stay on Edge 1.  Add the twisted Fourier coefficient and prove the per-slice exact expansion plus
the `v3(zeta) = v3(eta)` normalization.  Do not begin the Sec7P padding/generalization (Edge 2)
until the first frozen edge is assembled; the class expansion and slice partition are now done.

