# HANDOFF 2026-10-14: amusical reglue done

- Branch `wip/amusical-reglue`.  HEAD before this doc: `49cda01`.
- Done: `CollatzMoonshot/AmusicalReglue.lean` has no `sorry` left.
  - Proved: `chernoff_duality`, `bwd_iter_affine`, `lt_bwd_iter_iff` (Lemma BW),
    `exists_reglue_sparseFS` (Π), `exists_reglue_sparseFS_amusical` (Π′), and the new
    `permFwdSurvivor_two_mul`.
  - Axioms: `propext, Classical.choice, Quot.sound`.  Full `lake build` is green (8948 jobs,
    `CollatzMoonshot` + `Maze`).
  - Ratified statements unchanged: the diff vs `5a89467` removes only `sorry` lines.
- New modules under `CollatzMoonshot/AmusicalReglue/`:
  - `BackwardStep.lean`: one backward step of the amusical map.
  - `GlueWith.lean`: `IsCutSet.glueWith`, gluing with a caller-chosen segment order.
  - `Segments.lean`: segments, `segMin`, `le_segMin_of_survivor`.
  - `WordOrder.lean`: a key with finite intervals and no ends gives an `≃ ℤ`.
  - `Cuts.lean`: indexed glue cuts plus a singleton-piece spine.
  - `Blocks.lean`: block word order, `survivor_mem`.
  - `General.lean`: `exists_reglue_of_gluable`, from which Π and Π′ both follow.
- The kickoff's Π′ paper route (E-run spine pieces) fails for `G = o(log X)`.
  - Mechanism: `permFwdSurvivor_two_mul`.
  - Replaced by spine points at non-periodic `y ≡ 1 (mod 6)`.
- Details: `HANDOFF-amusical-reglue.md`.
- Next: nothing in scope.  `AmusicalNearCycleEntropy.lean` belongs to another treadmill.
- `box done --green` was signalled.
