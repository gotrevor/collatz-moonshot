# Fourier treadmill handoff — 2026-10-24

## Checkpoint

Proved `CollatzMoonshot.Conjugacy.sum_norm_sq_fourierCoeff` without changing its frozen
statement.  The proof reindexes the defining range sums onto `ZMod (2^(j+1))` and proves the
needed finite Parseval identity directly from the primitive standard additive character:

- `zmodParseval` expands squared norms into a double sum and uses `AddChar.sum_mulShift` to
  collapse the inner character sum to the diagonal;
- `fourierCoeff_eq_zmod` identifies the repository's positive-exponent normalization with that
  `ZMod` transform;
- every value of `beyondSign` is `1` or `-1`, so its unnormalized squared energy is exactly the
  period and the two normalization factors leave total energy `1`.

The earlier `lowFreqDecay_of_twoAdicFreqDecay` and `fourierCoeff_succ` proofs remain intact.  Two
declarations in the scoped file remain unproved:

1. `bias_div_le_lowFreq_add_tail`
2. `biasDecays_of_lowFreqDecay`

Following the kickoff's dependency order, the next target is `bias_div_le_lowFreq_add_tail`.

## Verification

- `lake env lean CollatzMoonshot/Conjugacy/Fourier.lean` — passes; only the two later unresolved
  declarations warn.
- `git diff --check` — passes.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-fourier --target
  CollatzMoonshot.Conjugacy.Fourier --axioms
  CollatzMoonshot.Conjugacy.sum_norm_sq_fourierCoeff` — `FORMALIZE-TIER GREEN`, 8719 jobs; the
  proved Parseval theorem has axioms `[Classical.choice, Quot.sound, propext]`.

## Current blocker and next attack

The next crux is the quantitative Fourier reduction `bias_div_le_lowFreq_add_tail`.  Start by
isolating the exact half-period antiperiodicity
`beyondSign j (r + 2^j) = -beyondSign j r`, then use it to prove that even Fourier frequencies
vanish.  Next formalize the half-window Fourier coefficient and the finite inversion identity for
`bias j`.  The low-frequency bound should then follow from Jordan's sine inequality, while the
high-frequency term should use the newly proved `sum_norm_sq_fourierCoeff` plus finite
Cauchy–Schwarz and the reciprocal-square tail estimate.  Keep these as named helper lemmas so each
analytic leaf can be checked independently.

No operator decision is needed; this remains a hard-but-doable finite Fourier estimate.
