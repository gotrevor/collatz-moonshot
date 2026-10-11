# HANDOFF 2026-10-11 — arc-band certificate complete

Both ordered targets in `ARC-BAND-CERTIFICATE-DIRECTION.md` are complete.  The host predicate
`sorry-free:CollatzMoonshot/Benchmark/ArcBandCertificate.lean` is met.

## Advance

`CollatzMoonshot/Benchmark/ArcBandCertificate.lean` now proves
`ArcBandCertificate.relaxedAboveUpperEdge` without `sorry`.

- The Lean interval checker transcribes `normalize`, `intersect`, the two parity steps, and iteration from
  `experiments/arc_band.py` using partial affine-sign comparisons.
- `normalize_sound`, `intersect_sound`, `symbolicStep_sound`, and `descend_sound` prove pointwise that every
  relaxed strategy remains inside every successfully computed symbolic descent.
- The checker verifies barycentric coefficient identities, positive-multiple edge constraints, nonzero
  `β` coefficients, and leaf emptiness.  `certificate0` and `certificate1` check both generated trees.
- `exists_beta_avoiding` chooses a point just left of any boundary point while avoiding the finite zero set
  of all comparison forms.  `RelaxedStrategy.mono` then moves a hypothetical strategy to that certified
  interior point.  Widths above the root ceiling are excluded directly by `RelaxedStrategy.width_le`.

The earlier item 1 theorem, `ArcDelayGame.finiteMemoryRelaxedValue_of_componentK`, was reviewed in source
and re-audited; its frozen statement and domination route remain intact.

## Verification

- `lake env lean CollatzMoonshot/Benchmark/ArcBandCertificate.lean` — PASS; no `sorry` warning.
- Direct execution of the three persistent `arc_band.py` controls (without pytest, unavailable offline) —
  PASS: edge-point control, polygon cover, and Python certificate-tree checker.
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot --target
  CollatzMoonshot.Benchmark.ArcBandCertificate --axioms
  CollatzMoonshot.Benchmark.ArcBandCertificate.relaxedAboveUpperEdge --allow
  CollatzMoonshot.Benchmark.ArcBandCertificate.certificate0._native.native_decide.ax_1_1 --allow
  CollatzMoonshot.Benchmark.ArcBandCertificate.certificate1._native.native_decide.ax_1_1` —
  `FORMALIZE-TIER GREEN` (8709 jobs).  Axioms are exactly `propext`, `Classical.choice`, `Quot.sound`, and
  the two direction-authorized native certificate artifacts.
- `~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot --target
  CollatzMoonshot.Benchmark.ArcDelayGame --axioms
  CollatzMoonshot.Benchmark.ArcDelayGame.finiteMemoryRelaxedValue_of_componentK` —
  `FORMALIZE-TIER GREEN` (8707 jobs); axioms exactly `propext`, `Classical.choice`, `Quot.sound`.
- `git diff --check` — PASS before the documentation checkpoint.

## Blocker / next attack

No blocker remains in this direction and there is no later in-scope objective.  The next lap should start
from a new operator kickoff rather than extending this completed certificate campaign.
