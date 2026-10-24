# Fourier pairing treadmill handoff — 2026-10-24

## Checkpoint

The first two ordered kickoff obligations are proved with their frozen statements unchanged.

For `pairTheta_far`, write `q = 3^t`, `N = 2^k`, and
`X = ((3 : ZMod N)⁻¹ ^ t * ξ).val`, the proof lifts `qX = ξ` in `ZMod N` to

```text
q X = ξ + N M
```

for an integer `M`.  If `q` divided `M`, the displayed equality would force `q ∣ ξ`, contrary
to the hypothesis.  Thus every integer `M - qz` has absolute value at least one.  The identity

```text
X/N - z = (M-qz)/q + ξ/(qN)
```

and the reverse triangle inequality give exactly
`(1 - ξ/N)/q ≤ |pairTheta ξ k t - z|`.

For `norm_latticeCoeff_le_pairBound`, the new helpers establish the exact paired-phase identity.
Reduction from `ZMod (2^(2i+3))` to `ZMod (2^(2i+2))` preserves `3⁻¹`, so the lower phase is the
square of the upper phase.  Factoring `E² + E = E(E+1)`, using `‖E‖ = 1`, and proving the
half-angle formula

```text
‖exp(-2πix) + 1‖ = 2 |cos(πx)|
```

gives exactly the middle coefficient `1/2 * pairCos`.  A two-level induction then applies the
triangle inequality and the three induction hypotheses at offsets `m`, `m+1`, and `m+2`.

## Verification

- `lake env lean CollatzMoonshot/Conjugacy/FourierPair.lean` — passes; the only remaining
  unresolved-declaration warning is `lowFreqDecay_of_pairBoundDecay`.

## Current blocker and next attack

The only remaining scoped obligation is `lowFreqDecay_of_pairBoundDecay`.  Split the level into
even and odd cases; the even subsequence is bounded directly by `pairBound ξ i 0`, while one
lattice unfolding bounds the odd subsequence by
`1/2 * pairBound ξ i 0 + 1/2 * pairBound ξ i 1`.  Apply `squeeze_zero` to both and combine the
two parity subsequences.
