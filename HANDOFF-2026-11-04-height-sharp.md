# HANDOFF 2026-11-04 — the height line to `C*` (`wip/orbit-word-law`)

Kickoff: `KICKOFF-2026-11-04-height-sharp.md`.  Gate: `sorry-free:CollatzMoonshot/Conjugacy/OrbitHeightSharp.lean`.

## TARGET MET

Both frozen targets are proved; statements byte-identical to the planting commit `eb111db`
(only the docstrings changed: "Believed, 90%" became the proof sketch).

    #print axioms heightLawBelowThreshold   -- [propext, Classical.choice, Quot.sound]
    #print axioms firstPassage_sharp        -- [propext, Classical.choice, Quot.sound]
    #print axioms heightLawUpTo_iff         -- [propext, Classical.choice, Quot.sound]

Checked from `/tmp/axchk/Ax.lean` with a `sorry` control (`sorryControl` shows `sorryAx`).
`heightLawUpTo_four`, `firstPassage_law`, `orbitWordLaw_of_le_four` unchanged and still clean.
`lake build CollatzMoonshot` green (8942 jobs).  No `native_decide`, `axiom` or `maxHeartbeats`.

## What carried the line (no fixed number was structural)

1. **Letter-`1` tolerance `1/100`.**  Not parametrised at all: for the word `u = [true]` the read-off's
   own `δ` is the tolerance.  `ScaleGood [true] δ η x n` already contains `WinGood [true] δ`, and the
   `1/100` half is used only to pass each stage (`start_passes`, `next_passes`), which needs no
   sharpness.  `readOff_chain` (in `OrbitHeightSharpReadOff.lean`) runs `wdev_chain` with `δ`.
2. **`numScales = 4000`.**  Replaced by `J` with `α^(−J) ≤ γ/4`, `γ = 1 − τβ`
   (`exists_alpha_inv_pow_le`).  `goodOddUpTo_whp` sums `stage_whp` over `range J`; every existing
   lemma (`stage_whp`, `dTV_chain`, `scaleGood_whp`) was already per-scale.
3. **Horizon `21/5`.**  New predicate `GoodOddUpTo δ τ n` (prefixes `T ≤ τ size n`), proved whp by
   `goodOddUpTo_of_stages`.  Read-off arithmetic is `readOff_arith`: with `δτ ≤ γ/8`,
   `η(J+1) ≤ γ/8`, `γ ℓ ≥ 4(2J+3)`, the passage below `x_J` cannot come before `τ size n`.
4. **`β ≤ 21/100` in `height_lower_of_goodOddUpTo`.**  Avoided: the argument is in `γ = 1 − τβ`
   directly.  `heightCorr` is bounded by `t / 2^K` with `K` a *constant* (`⌈4τ/ε⌉`), needing only
   `γ size m ≥ 2(K+1)` — linear, no exponential-vs-linear lemma (`heightCorr_le_of_goodOddUpTo`).
5. **Even reduction.**  Horizon `τ = τ₁ + μ`, `μ = (1 − τ₁β)/(2β)`; `τ₁ a ≤ μ size m` gives
   `t − a ≤ τ size m` (`abs_height_sub_line_le_two_pow_mul_upTo`, `not_badHeight_two_pow_mul`,
   `heightLawUpTo_of_one_le`).  `heightLawBelowThreshold` applies it at `max τ 4` and uses
   `HeightLawUpTo.mono`.
6. `firstPassage_sharp`: `firstPassage_law`'s proof at `τ = (1−θ)/β + min ε (θ/(2β))`.

## Files

- `CollatzMoonshot/Conjugacy/OrbitHeightSharpReadOff.lean` (new): `GoodOddUpTo`, `readOff_chain`,
  `readOff_arith`, `goodOddUpTo_of_stages`, `goodOddUpTo_whp`.
- `CollatzMoonshot/Conjugacy/OrbitHeightSharpLine.lean` (new): odd core, even reduction,
  `HeightLawUpTo.mono`.
- `CollatzMoonshot/Conjugacy/OrbitHeightSharp.lean`: assembly; 0 `sorry`.

## Next (operator's call)

- `docs/notes/` write-up of the height line and first passage (lane rule: neutral note, pinned commit).
- `logNormal_of_orbitWordLaw` (`ChampernowneLog.lean`), still open under `logNormal_of_le_four`.
- `StageWordLaw` (per-stage, not log-density) remains the open node beyond log density.
