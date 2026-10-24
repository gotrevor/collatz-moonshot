# Fourier treadmill handoff — 2026-10-24

## Checkpoint

Proved `CollatzMoonshot.Conjugacy.bias_div_le_lowFreq_add_tail` without changing its frozen
statement.  The quantitative reduction now follows the docstring's finite Fourier argument:

- `beyondSign_add_half_period` proves the exact half-period sign flip, and
  `fourierCoeff_eq_zero_of_even` kills the even Fourier frequencies;
- `bias_eq_fourier_window` and `bias_eq_sum_range_fourier_window` identify `bias` with the DFT
  pairing against the first-half indicator;
- `norm_half_geom_sum_le` evaluates the odd half-window geometric sum and applies Jordan's sine
  inequality, while the two conjugate-symmetry lemmas pair positive and negative frequencies;
- `bias_div_le_weighted_fourier` gives the weighted finite-frequency bound;
- `two_mul_sum_sq_fourierCoeff_Ico_le`, Parseval, finite Cauchy–Schwarz, and
  `sum_Ioc_inv_sq_le_sub` give the sharp `sqrt (2 / K)` tail.

The earlier `lowFreqDecay_of_twoAdicFreqDecay`, `fourierCoeff_succ`, and
`sum_norm_sq_fourierCoeff` proofs remain intact.  One declaration in the scoped file remains
unproved:

1. `biasDecays_of_lowFreqDecay`

Following the kickoff's dependency order, this final declaration is the next target.

## Verification

- `lake env lean CollatzMoonshot/Conjugacy/Fourier.lean` — passes; the only unresolved
  declaration warning in the file is `biasDecays_of_lowFreqDecay`.
- `git diff --check` — passes.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-fourier --target
  CollatzMoonshot.Conjugacy.Fourier --axioms
  CollatzMoonshot.Conjugacy.bias_div_le_lowFreq_add_tail` — `FORMALIZE-TIER GREEN`, 8719 jobs;
  the proved reduction has axioms `[Classical.choice, Quot.sound, propext]`.

## Current blocker and next attack

The remaining proof is the finite-set epsilon argument in `biasDecays_of_lowFreqDecay`.  Given
`0 < ε`, choose a natural `K ≥ 1` with `sqrt (2 / K) < ε / 2` (an Archimedean choice such
as `K > 8 / ε²` suffices).  For the finite set `(range (K+1)).filter Odd`, use `h` and the
finite-sum `Tendsto` API to show
`j ↦ ∑ ξ, 2 * ‖fourierCoeff j ξ‖ / ξ` tends to zero.  Eventually it is below
`ε / 2`; combine this with `bias_div_le_lowFreq_add_tail`, then remove the absolute value to
prove the `BiasDecays` limit.  No operator decision is needed.
