# HANDOFF 2026-10-14: amusical oddrewire done

- Branch `wip/amusical-oddrewire`.  HEAD before this doc: `6f9d945`.
- Done: `CollatzMoonshot/AmusicalOddRewire.lean` has no `sorry` left.
  - Proved: `fwdSurvivor_three_separation_of`, `exists_oddRewire` (T1★) and `tail_threshold` (TT).
  - Axioms: `propext, Classical.choice, Quot.sound`.  Full `lake build` is green (8936 jobs).
- New modules under `CollatzMoonshot/AmusicalOddRewire/`:
  - `CutSet.lean`: `IsCutSet.glue`, reconnection along any cut set.
  - `Glue.lean`: GL `exists_glue`, with `GluePt`.
  - `OddTails.lean`: `exists_late_odd`, `exists_early_odd`, `gluePt_odd_of_infinite`.
  - `Threshold.lean`: TT helpers.
- Details: `HANDOFF-amusical-oddrewire.md`.
- Next, optional and outside the scope of this run: NG★ (kickoff item 9).
  - First state it in Lean.
  - Then generalize `glueChange` to a stage-dependent `S q`, for example `S_k = {n ≡ 1 mod 6^max k 2}`.
- `box done --green` was signalled.
