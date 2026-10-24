# Fourier treadmill handoff — 2026-10-24

## Checkpoint

Proved `CollatzMoonshot.Conjugacy.lowFreqDecay_of_twoAdicFreqDecay` without changing its frozen
statement.  The proof now factors through two public helpers in
`CollatzMoonshot/Conjugacy/Fourier.lean`:

- `fourierCoeff_add_period`: `fourierCoeff j` is periodic in its frequency with period
  `2^(j+1)`;
- `padicInt_appr_natCast`: the level-`n` approximant of an embedded natural is its remainder
  modulo `2^n`.

For an odd natural frequency `ξ`, the p-adic norm criterion proves `(ξ : ℤ_[2])` is a unit.
`TwoAdicFreqDecay` therefore supplies convergence along its p-adic approximants, and the two
helpers identify every term of that sequence with the fixed-frequency coefficient.

Four declarations in the scoped file remain unproved:

1. `sum_norm_sq_fourierCoeff`
2. `bias_div_le_lowFreq_add_tail`
3. `biasDecays_of_lowFreqDecay`
4. `fourierCoeff_succ`

Following the kickoff's suggested dependency order, the next target is `fourierCoeff_succ`.

## Verification

- `lake env lean CollatzMoonshot/Conjugacy/Fourier.lean` — passes; only the four pre-existing
  unresolved declarations warn.
- `git diff --check` — passes.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-fourier --target
  CollatzMoonshot.Conjugacy.Fourier --axioms
  CollatzMoonshot.Conjugacy.lowFreqDecay_of_twoAdicFreqDecay` — `FORMALIZE-TIER GREEN`, 8719 jobs;
  the proved edge has axioms `[Classical.choice, Quot.sound, propext]`.

## Current blocker and next attack

The next crux is the odd-half reindexing in `fourierCoeff_succ`.  Split the level-`j+1` sum into
even and odd indices.  The even half reduces directly to `fourierCoeff j ξ`.  For the odd half,
prove that `beyondSign j` is periodic modulo `2^(j+1)` from
`tstep_iterate_add_mul_two_pow`, then reindex `s ↦ (3*s+2) % 2^(j+1)` using the supplied inverse
`u` (`3*u % 2^(j+1)=1`).  The newly proved `fourierCoeff_add_period` handles frequency reductions
needed by this and later steps.

No operator decision is needed; this is a hard-but-doable Lean reindexing proof.
