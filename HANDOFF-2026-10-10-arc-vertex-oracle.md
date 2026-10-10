# HANDOFF 2026-10-10 — arc-band vertex oracle proved

Continued item 2 of `ARC-BAND-CERTIFICATE-DIRECTION.md`.  The scoped target
`ArcBandCertificate.relaxedAboveUpperEdge` remains open.

## Advance

`CollatzMoonshot/Benchmark/ArcBandCertificate.lean` now contains the first load-bearing checker layer:

- real and rational evaluation of certificate affine forms, with negation and subtraction identities;
- `Aff.eval_affineCombination`, proving exact preservation of three-term affine combinations;
- `Aff.eval_pos_of_barycentric`, proving strict positivity throughout a triangle's strict interior from
  nonnegative vertex values and one strict vertex value;
- executable `vertexSign`, matching Python's three-way vertex sign oracle;
- kernel proofs `vertexSign_eq_sound`, `vertexSign_gt_sound`, and `vertexSign_lt_sound` for all three
  successful oracle outcomes.

This removes the mathematical uncertainty in the vertex sign mechanism.  The existing headline `sorry` is
unchanged and disclosed.

## Verification

- `lake env lean CollatzMoonshot/Benchmark/ArcBandCertificate.lean` — PASS (only the existing headline
  `sorry`; publish-tier lints ignored by policy).
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot --target
  CollatzMoonshot.Benchmark.ArcBandCertificate` — `FORMALIZE-TIER GREEN` (8709 jobs).
- `git diff --check` — PASS.

## Current blocker / next attack

The target remains blocked only by doable formalization, not an external condition.  Implement symbolic
closed intervals and the exact `normalize`/`intersect`/`step` computation from `experiments/arc_band.py`.
Prove first that one symbolic step evaluates to a superset of the semantic operator `F`; then iterate this
to show any `RelaxedStrategy` is contained in every evaluated descent.  After that, connect leaf emptiness
to the proved vertex oracle, validate the generated trees by `native_decide`, and finish the boundary shift.
