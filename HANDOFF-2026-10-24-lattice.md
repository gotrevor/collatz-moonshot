# Fourier lattice treadmill handoff — 2026-10-24

## Final checkpoint

The kickoff is complete.  All five frozen statements are unchanged and proved, and both
`CollatzMoonshot/Conjugacy/FourierSup.lean` and
`CollatzMoonshot/Conjugacy/FourierLattice.lean` are sorry-free.

- `lowFreqDecay_of_fixedFreqExpDecay` rewrites the exponential majorant as a geometric
  sequence with ratio `2^(-(1/2+δ)) < 1` and squeezes the coefficient norms to zero.
- `supFreqDecay_of_sqrtBound` uses `sqrt j → ∞`, hence `C / sqrt j → 0`, uniformly in
  every odd frequency.
- `twoAdicFreqDecay_of_supFreqDecay` proves every positive-level approximant of a 2-adic unit
  is odd: otherwise both the approximation error and the approximant are divisible by `2`,
  contradicting the unit norm.

- `fourierCoeff_eq_latticeCoeff` is proved by induction on the level.  Reduction through
  `ZMod.castHom` preserves `3⁻¹`, giving the two lower-level frequencies.  In the phase,
  `3a = 1` for `a = 3⁻¹` gives `x(1-4a) = -ax` modulo `2^(n+2)`; integer-periodicity of
  the complex exponential turns this congruence into exactly `latticePhase`.
- `fourierCoeff_eq_latticeCoeff_zero` specializes the formula at `m = 0` and uses the
  `2^(j+1)` frequency periodicity to replace the canonical `ZMod` representative by `ξ`.

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

Exact lattice gate:

```text
~/personal/bin/lean-green ~/src/collatz-moonshot-fourier \
  --target CollatzMoonshot.Conjugacy.FourierLattice \
  --import CollatzMoonshot.Conjugacy.FourierLattice \
  --axioms CollatzMoonshot.Conjugacy.fourierCoeff_eq_latticeCoeff \
  --axioms CollatzMoonshot.Conjugacy.fourierCoeff_eq_latticeCoeff_zero

✅ FORMALIZE-TIER GREEN
```

Both lattice declarations report exactly `[propext, Classical.choice, Quot.sound]`.  `rg` finds
no `sorry`, `sorryAx`, `native_decide`, or declared axiom in either scoped module.

## Current blocker and next attack

None.  The host predicate `sorry-free:CollatzMoonshot/Conjugacy/FourierLattice.lean` and the full
ordered kickoff objective are met.  No stretch objective was authorized; preserve this green
checkpoint and return to the operator.
