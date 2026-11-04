# HANDOFF 2026-11-04: the orbit word law

Branch `wip/orbit-word-law`.  Kickoff: `KICKOFF-2026-11-04-orbit-word-law.md`.

## State

`orbitWordLaw_of_le_four` (statement byte-identical) is proved in `OrbitWordLaw.lean` from 16 open
nodes, each a `Prop` defined in a sibling and held open by a `sorry` theorem in `OrbitWordLaw.lean`
(so the host's one-file gate counts exactly the open work; the siblings carry no `sorry`):

- `OrbitWordLawOrbit.lean`: `StagePasses`, `GoodOddOfStages`, `LocGoodPassLoc`.
- `OrbitWordLawProb.lean`: `CardMatchSet`, `CardMatchOne`, `CardMatchTwo`, `SumSqWdevLe`,
  `CardBadBlockLe`, `WinGoodOfBlocks`, `WinGoodModIff`, `ProbPeriodicLe`, `WinGoodWhp`.
- `OrbitWordLawDensity.lean`: `LogDens0OfWindow`, `LogDens0OddPart`, `SummableLargeTwoAdic`,
  `NotBadStartOfGoodOdd`.

Rule: prove a node as `theorem fooOf (h₁ : Sub₁) … : Foo` in a sibling (sorry-free), and close it in
`OrbitWordLaw.lean` by citing the sub-node theorems.  Never let a sibling cite a `sorry`.

Proved (kernel): the chain `dTV_chain` (Tao's `stabilization_atCX` at every scale, data processing,
`dTV_triangle`, `passLoc_passLoc`); the Syracuse bridge `syr_iterate_eq_tstep`, `tstep_between`,
`valSum_add`, `passes_passLoc`; window-count algebra `wdev_add`, `wdev_shift`, `abs_wdev_le`;
the glue `goodOdd_whp`, `stage_whp`, `locGood_whp`, `scaleGood_whp`; density helpers
`LogDens0.mono/.or`, `logDens0_of_summable`, `logDens0_of_bdd`, `orbitWordLaw_iff`.

## Design (differs from the kickoff where simpler)

- Only `o(1)` exceptional probability is needed at each scale (3000 scales, fixed), so large
  deviations are replaced by Chebyshev on boundedly many blocks of length `≈ δ η log₂ x / 8`.
- Location event = prefix-goodness (lengths in `[hgt η x, lam x]`, `lam x = ⌊log₂ x / 20⌋`) for `u`
  and for `[true]` within `1/100`; descent below the next scale is derived from the `[true]`
  frequency (`StagePasses`), not a separate event.
- Even starts: `GoodOdd` asks for `5T ≤ 21 size n` letters (4.2×), absorbing `a ≤ size m / 15`.

## Next

`StagePasses` (then `LocGoodPassLoc` from it), `GoodOddOfStages` (the read-off), then the
Terras/Chebyshev chain, then density.  `#print axioms orbitWordLaw_of_le_four`: `sorryAx` until
all 16 close.

## Checkpoint (lap end)

HEAD after this commit on `wip/orbit-word-law`; no uncommitted Lean edits.  Build:
`lake build CollatzMoonshot.Conjugacy.OrbitWordLaw` green.  Sorry count of the gated file: 16.

## Lap 2 (2026-11-04, autonomous)

Proved, axioms `propext, Classical.choice, Quot.sound`:
- `stagePasses` (`OrbitWordLawStage.lean`, `stagePasses_holds`).  `StagePasses` restated with cover
  `20 (D + 2) + 4H` (roomier than the planted `2⌈6(D+1)⌉ + 4H`).
- `locGoodPassLoc` (`locGoodPassLoc_holds`, same file).
- `goodOddOfStages` (`OrbitWordLawReadOff.lean`, `goodOddOfStages_holds`).  `numScales` is now
  `4000` (`α^(−3999) ≤ 1/50` via `decide +kernel` on `50·1000^3999 ≤ 1001^3999`).

Sorry count of the gated file: 13.  Left: the probabilistic chain (`CardMatchSet` …
`WinGoodWhp`) and density (`LogDens0OfWindow`, `LogDens0OddPart`, `SummableLargeTwoAdic`,
`NotBadStartOfGoodOdd`).
