# Fourier lattice treadmill handoff — 2026-10-24

## Current checkpoint

The first kickoff stage is complete: all three frozen edge statements in
`CollatzMoonshot/Conjugacy/FourierSup.lean` are proved.

- `lowFreqDecay_of_fixedFreqExpDecay` rewrites the exponential majorant as a geometric
  sequence with ratio `2^(-(1/2+δ)) < 1` and squeezes the coefficient norms to zero.
- `supFreqDecay_of_sqrtBound` uses `sqrt j → ∞`, hence `C / sqrt j → 0`, uniformly in
  every odd frequency.
- `twoAdicFreqDecay_of_supFreqDecay` proves every positive-level approximant of a 2-adic unit
  is odd: otherwise both the approximation error and the approximant are divisible by `2`,
  contradicting the unit norm.

The two frozen lattice statements remain open.  The next attack is
`fourierCoeff_eq_latticeCoeff`, by the prescribed induction on the level, followed by its
`m = 0` corollary.

## Verification

Exact checkpoint gate:

```text
~/personal/bin/lean-green ~/src/collatz-moonshot-fourier \
  --target CollatzMoonshot.Conjugacy.FourierSup \
  --import CollatzMoonshot.Conjugacy.FourierSup \
  --axioms CollatzMoonshot.Conjugacy.lowFreqDecay_of_fixedFreqExpDecay \
  --axioms CollatzMoonshot.Conjugacy.supFreqDecay_of_sqrtBound \
  --axioms CollatzMoonshot.Conjugacy.twoAdicFreqDecay_of_supFreqDecay

✅ FORMALIZE-TIER GREEN
```

All three declarations report exactly `[propext, Classical.choice, Quot.sound]` (sorted order
varies in the gate output).

## Current blocker

No external blocker.  The remaining crux is the modular-arithmetic and complex-phase alignment
in the induction step of `fourierCoeff_eq_latticeCoeff`.
