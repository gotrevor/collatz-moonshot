# Fourier treadmill handoff — 2026-10-24

## Checkpoint

Proved `CollatzMoonshot.Conjugacy.biasDecays_of_lowFreqDecay` without changing its frozen
statement.  The proof follows the advertised finite-frequency epsilon argument:

- the real sequence `K ↦ sqrt (2 / K)` tends to zero by composing division at infinity with
  continuity of `Real.sqrt`, so a fixed `K ≥ 1` makes the tail smaller than `ε / 2`;
- `LowFreqDecay` makes each weighted coefficient `2 * ‖fourierCoeff j ξ‖ / ξ` tend to zero, and
  `tendsto_finsetSum` combines this over the finite set of odd `ξ ≤ K`;
- `bias_div_le_lowFreq_add_tail` then bounds the normalized absolute bias by two terms smaller
  than `ε / 2`.

The review reconstructed the route from the frozen source, kickoff, history, and current proof
dependencies.  The quantitative reduction is exactly the load-bearing input for this last edge;
no route correction was needed, and the five frozen statements plus `LowFreqDecay`,
`TwoAdicFreqDecay`, `fourierCoeff`, and `beyondSign` retain their original shapes.

All five declarations assigned by `KICKOFF-2026-10-24-fourier.md` are now proved, and
`CollatzMoonshot/Conjugacy/Fourier.lean` is sorry-free.

## Verification

- `lake env lean CollatzMoonshot/Conjugacy/Fourier.lean` — passes with no unresolved-declaration
  warning.
- `rg -n "\\bsorry\\b|sorryAx" CollatzMoonshot/Conjugacy/Fourier.lean` — no matches.
- `git diff --check` — passes.
- `/Users/gotrevor/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-fourier --target
  CollatzMoonshot.Conjugacy.Fourier --axioms
  CollatzMoonshot.Conjugacy.biasDecays_of_lowFreqDecay` — `FORMALIZE-TIER GREEN`, 8719 jobs;
  the final edge has axioms `[Classical.choice, Quot.sound, propext]`.

## Current blocker and next attack

There is no remaining scoped blocker or unproved declaration in `Fourier.lean`; the host
predicate `sorry-free:CollatzMoonshot/Conjugacy/Fourier.lean` is met.  Stop this campaign with
`box done`.  A later, separately authorized research campaign could attack the open proposition
`LowFreqDecay` itself through phase cancellation in `fourierCoeff_succ`, but that is beyond this
formalization checkpoint.
