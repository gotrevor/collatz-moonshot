# HANDOFF: Front B board repair 🧨 — DONE (2026-08-23)

**This lap's finding**: the boarded Route-2 targets (`Compression`, `BoundedDen`) were
**FrontB in disguise** - word powers `wpow v j` keep the member value while `circuits`
telescopes and `den` explodes, so bounding either quantity over *all* nontrivial integral
words is equivalent to asserting no counterexample exists.  Proved axiom-free
(`naiveCompression_iff_frontB`, `naiveBoundedDen_iff_frontB`).  Repaired by quantifying
over `Primitive` words, with the decomposition `exists_primitive_root` carrying the wiring.
Full story: `FRONT-B-ROUTES.md` §2026-08-23; machinery: `CollatzMoonshot/FrontB/Powers.lean`.

## State

- `lake build` green; committed `55ff482`.
- Axiom audit (observed in real output, 2026-08-23): both degeneracy theorems and
  `frontB_of_compression` = base three only; `frontB_of_compression_le_91` = base three
  + exactly `hercher_min_circuit_count`; `finite_shapes_of_boundedDen` = base three +
  exactly `baker_bounded_difference`.
- New THEOREM-grade axiom `hercher_min_circuit_count` (Hercher 2023, m-cycles need
  m ≥ 92; primary source verified 2026-08-22, summary in `papers/`).

## Next attack

- **The sharpened Route-2 target**: `frontB_of_compression_le_91` reduces Front B to
  *"a primitive nontrivial integral cycle has ≤ 91 circuits"* - one statement, no ladder
  extrapolation.  Nothing formal exists toward proving compression itself; the prose map
  (`FRONT-B-ROUTES.md`) stands, with the new doctrinal note that compression must be
  sign-blind (positivity lives in the ladder).
- Alternative threads: Knight-style second extremal word family (~12%, now `BoundedDen`
  on primitive words), Front A route map (`FRONT-A-ROUTES.md`, absorbed 2026-08-23 but
  unworked), `PI02-SKETCH.md`.
