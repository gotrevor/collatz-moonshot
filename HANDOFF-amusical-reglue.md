# HANDOFF amusical-reglue

## Done
- `chernoff_duality`, `bwd_iter_affine` (via sharper `bwd_iter_affine_le`: `|E| ≤ 4^i − 3^i`),
  `lt_bwd_iter_iff` proved (commit e2a29c2).  Helpers: `AmusicalReglue/BackwardStep.lean`.

## Open
- `exists_reglue_sparseFS` (Theorem Π), then `exists_reglue_sparseFS_amusical` (Π′).
  Next: read `AmusicalOddRewire/Glue.lean` (`IsCutSet`, `exists_glue`) to decide whether to reuse it
  or to build the block word as a list-concatenation bijection `ℤ ≃ chain points`.
