# Fourier pairing treadmill handoff — 2026-10-24

## Final checkpoint

The kickoff is complete.  All three ordered obligations are proved with their frozen statements
unchanged, and `CollatzMoonshot/Conjugacy/FourierPair.lean` is sorry-free.

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

Finally, `lowFreqDecay_of_pairBoundDecay` splits an arbitrary level into `2i` or `2i+1`.  At
even levels, `fourierCoeff_eq_latticeCoeff_zero` and the pairing estimate give the direct bound
by `pairBound ξ i 0`.  At odd levels, one lattice unfolding and the unit norm of the phase give

```text
‖fourierCoeff (2i+1) ξ‖ ≤ 1/2 pairBound ξ i 0 + 1/2 pairBound ξ i 1.
```

Both offsets tend to zero by `PairBoundDecay`, so the parity-uniform epsilon argument proves
`LowFreqDecay`.

## Verification

- `lake env lean CollatzMoonshot/Conjugacy/FourierPair.lean` — passes with no unresolved-
  declaration warning.
- `rg -n "\\bsorry\\b|sorryAx|native_decide|^axiom "
  CollatzMoonshot/Conjugacy/FourierPair.lean` — no matches.
- `~/personal/bin/lean-green ~/src/collatz-moonshot-fourier --target
  CollatzMoonshot.Conjugacy.FourierPair --import CollatzMoonshot.Conjugacy.FourierPair --axioms
  CollatzMoonshot.Conjugacy.pairTheta_far --axioms
  CollatzMoonshot.Conjugacy.norm_latticeCoeff_le_pairBound --axioms
  CollatzMoonshot.Conjugacy.lowFreqDecay_of_pairBoundDecay` — `FORMALIZE-TIER GREEN`, 8721 jobs;
  all three declarations report exactly `[Classical.choice, Quot.sound, propext]`.
- `~/personal/bin/lean-green ~/src/collatz-moonshot-fourier` — `FORMALIZE-TIER GREEN`, 8857
  jobs.
- `git diff --check` — passes.  The diff against kickoff commit `ea2d3ae` confirms the five
  frozen definitions/statements remain unchanged; only proof bodies and new helper declarations
  were added to `FourierPair.lean`.

## Current blocker and next attack

There is no remaining scoped blocker.  After the scoped axiom gate and full repository build are
green, the host predicate `sorry-free:CollatzMoonshot/Conjugacy/FourierPair.lean` is met; stop
this campaign with `box done`.  `PairBoundDecay` intentionally remains an open `Prop`, not a
proof obligation in this kickoff.
