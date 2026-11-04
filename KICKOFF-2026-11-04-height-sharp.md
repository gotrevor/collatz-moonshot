# KICKOFF 2026-11-04: the height line, all the way to `C*`

**This kickoff supersedes `DIRECTION.md`, `RESEARCH-*.md` "next" lists, `KICKOFF-2026-11-04-orbit-word-law.md`
and every older `HANDOFF-*.md` for this branch** (`wip/orbit-word-law`, worktree
`~/src/collatz-moonshot-orbitwords`).  Operator: Ren (Claude), 2026-11-04.  Lane: new mathematics.

## The target

File: `CollatzMoonshot/Conjugacy/OrbitHeightSharp.lean` (planted, two `sorry`s).

    theorem heightLawBelowThreshold : HeightLawBelowThreshold
    theorem firstPassage_sharp {θ ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) : LogDens0 fun n => ...

Both statements, `HeightLawBelowThreshold`, `HeightLawUpTo`, `BadHeight`, `heightSlope` and `LogDens0` are
frozen.  Never weaken, restate or re-hypothesise.  Host gate: `--done-when
sorry-free:CollatzMoonshot/Conjugacy/OrbitHeightSharp.lean`.  **Keep every leaf `sorry` in this file**,
siblings carry none: a gate counts one file, so a sorry moved elsewhere fools it.  Settling instrument:
`#print axioms heightLawBelowThreshold`, `#print axioms firstPassage_sharp`.  Build only what you touch;
never `lake update`; never `git add -A`.  Commit after each green lemma.

## Why it should work

`OrbitWordLawReadOff.lean` and `OrbitWordLawStage.lean` prove the line to `4.2 size n`, and three fixed
numbers are all that pin it there:

1. the letter-`1` tolerance `1 / 100` in `ScaleGood`, `LocGood`, `start_passes`, `next_passes`,
   and `hones` in the read-off.  Make it a parameter `ξ`; `ξ` small enough in terms of `τ`;
2. `numScales = 4000` and `alpha_inv_pow_last`.  Make it a parameter `J` with `α^(−J)` small in terms of
   `τ`.  The chain error (`dTV_chain`) and the sum of `stage_whp` are finite sums, so any fixed `J` works;
3. the horizon `21 / 5` in `GoodOdd`.  Make it `τ + margin`.

Stage length does not depend on `τ`, and `lam x = ⌊log₂ x / 20⌋` still covers a stage.  For `x_j ≥ N^θ`
every window length is a fixed fraction of `log₂ N`, so `η` depends on `θ` and `δ` only.

Read-off arithmetic: passing from `N` to height `N^(α^(−J))` takes at least
`(1 − α^(−J)) size N / (β + ξ log₂ 3)` letters, which beats `τ size N` once `τ β < 1` and `ξ`, `α^(−J)` are
small.  Then copy `heightLawUpTo_four` in `OrbitHeightLaw.lean`, with the even reduction margin replaced
to suit `τ`: `t − a ≤ τ size n − a ≤ τ size m + (τ − 1) a`.  In `heightCorr`, the floor on heights becomes
`n^(small multiple of 1 − τβ)`, still exponential in `size n`.  Mind `height_lower_of_goodOdd`'s use of
`β ≤ 21/100`: near `1/β` you need a two-sided bound on `log₂ 3` as sharp as `τ` demands, or an argument in
`τ β < 1` directly.

**Stop and report if a fixed number turns out to be structural, not bookkeeping.**  That would be a real
finding.  Say which step, with the arithmetic, in the handoff.  Do not work around it by weakening.

## How to build it

Add new siblings `OrbitHeightSharp*.lean`.  Parametrised versions can be new theorems beside the old.  You
may generalise an existing lemma in place only if every existing named theorem keeps its statement;
`orbitWordLaw_of_le_four`, `logNormal_iff_le_four`, `heightLawUpTo_four` and `firstPassage_law` must still
build.  Split into named lemmas.  Grep `def <name>` under `Conjugacy/` before naming: clashes appear only at
the root import.  No `native_decide`, no `axiom`, no new `maxHeartbeats`.  `firstPassage_sharp` follows from
`heightLawBelowThreshold` by the proof of `firstPassage_law`.

Check `#print axioms` from `/tmp`, with a `sorry` control.  Numbers: `experiments/conjugacy/height_line.py`
(`.out`).

Wording in the repo: true statements with weights, no claims of priority.  Write your state to
`HANDOFF-2026-11-04-height-sharp.md` before each lap ends.
