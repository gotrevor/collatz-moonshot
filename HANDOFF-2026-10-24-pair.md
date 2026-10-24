# Fourier pairing treadmill handoff — 2026-10-24

## Checkpoint

The first ordered kickoff obligation, `pairTheta_far`, is proved with its frozen statement
unchanged.  Writing `q = 3^t`, `N = 2^k`, and
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

## Verification

- `lake env lean CollatzMoonshot/Conjugacy/FourierPair.lean` — passes; the only unresolved-
  declaration warnings are the two later kickoff obligations.

## Current blocker and next attack

The route-decisive remaining obligation is `norm_latticeCoeff_le_pairBound`.  Next introduce
the reduction-of-inverse helper from modulus `2^(2i+3)` to `2^(2i+2)`, prove the exact norm
identity for `latticePhase ξ (2i) m + latticePhase ξ (2i+1) m`, and use it in the advertised
two-level induction.  After that, discharge `lowFreqDecay_of_pairBoundDecay` by the even/odd
squeeze.
