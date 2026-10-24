# Fourier treadmill handoff — 2026-10-24

## Checkpoint

Proved `CollatzMoonshot.Conjugacy.fourierCoeff_succ` without changing its frozen statement.  The
proof splits the level-`j+1` numerator into even and odd inputs.  The even half is the level-`j`
coefficient directly.  For the odd half it proves and uses:

- `beyondSign_congr_mod`: the beyond-Terras sign depends only on the input modulo `2^(j+1)`;
- `sum_affineThreeMod`: when `3u ≡ 1 (mod n)`, the map `s ↦ (3s+2) mod n` permutes `range n`,
  with the explicit inverse `t ↦ u(t+n-2) mod n`;
- exact periodicity and phase helpers for the additive character, including the factor
  `exp(2πi ξ(1-4u)/2^(j+2))`.

The prior checkpoint's `lowFreqDecay_of_twoAdicFreqDecay` proof remains intact.  Three declarations
in the scoped file remain unproved:

1. `sum_norm_sq_fourierCoeff`
2. `bias_div_le_lowFreq_add_tail`
3. `biasDecays_of_lowFreqDecay`

Following the kickoff's dependency order, the next target is `sum_norm_sq_fourierCoeff`.

## Verification

- `lake env lean CollatzMoonshot/Conjugacy/Fourier.lean` — passes; only the three remaining
  pre-existing unresolved declarations warn.
- `git diff --check` — passes.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-fourier --target
  CollatzMoonshot.Conjugacy.Fourier --axioms CollatzMoonshot.Conjugacy.fourierCoeff_succ` —
  `FORMALIZE-TIER GREEN`, 8719 jobs; the proved recursion has axioms
  `[Classical.choice, Quot.sound, propext]`.

## Current blocker and next attack

The next crux is Parseval in `sum_norm_sq_fourierCoeff`.  Expand both squared norms using complex
conjugation, interchange the finite sums, and prove the character orthogonality identity over
`range (2^(j+1))`: the frequency sum is the period at equal residues and zero otherwise.  The
new `beyondSign_congr_mod` and additive-character periodicity pattern are available, while mathlib's
`IsPrimitiveRoot.geom_sum_eq_zero` or the `ZMod` DFT/additive-character API should discharge the
orthogonality leaf.  Finish with `beyondSign j r ∈ {1,-1}`, hence squared modulus one.

No operator decision is needed; this is a hard-but-doable finite Fourier identity.
