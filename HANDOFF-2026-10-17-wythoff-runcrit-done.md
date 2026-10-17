# HANDOFF 2026-10-17: wythoff-runcrit DONE

Branch `wip/wythoff-runcrit-m`, HEAD `07ee81b` (before this doc's commit).  Kickoff:
`KICKOFF-2026-10-17-wythoff-runcrit.md`; running notes: `HANDOFF-wythoff-runcrit.md`.

## Done

`CollatzMoonshot/WythoffRunCriterion.lean` is sorry-free; `lake build
CollatzMoonshot.WythoffRunCriterion` green, no warnings.  Axioms of `runCriterion_of_weyl`,
`n3_infinite_runs_of_weyl`, `runSystem_phaseVec_iff`: `[propext, Classical.choice, Quot.sound]`.
No ratified statement changed.

* `f43dcef` `linearIndependent_freqVec` (helper `eq_zero_of_natDegree_lt`).
* `89b8bcf` `exists_runBox` (helpers `fresh_step`, `top_step`, `std_step`); headline complete.
* `07ee81b` `runSystem_phaseVec_of_odd`; exact correspondence complete.

`RunCriterion` (from `WythoffPisot`) is now a theorem modulo the literature hypothesis
`WeylEquidistributionMulti`, and Theorem N3 is conditional on Weyl alone.

## Next steps (later layers, not started)

1. Positive density of long-run up-points: one `Tendsto` step from the limit inside
   `setOf_fract_mem_openBox_infinite`.
2. Necessity half of the zonotope criterion.
3. Mirror side (classify Theorem M).
4. Wire `CollatzMoonshot.WythoffRunCriterion` into `CollatzMoonshot.lean`; open the PR from this
   branch (host pushes).
