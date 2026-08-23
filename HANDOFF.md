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

## Thread pulls this session (2026-08-23, so nothing gets lost)

1. **Pulled "attack Compression"** → found and repaired the power degeneracy (above);
   sharpened target `frontB_of_compression_le_91` now stands.  Commits `55ff482`,
   `c8430a0`.
2. **Pulled Thread 2 (second extremal family)** → `experiments/knight_reach.py` census,
   `k ≤ 16`: the exact-identity trick's reach beyond balanced words is a **chance floor**
   (expected sporadic hits ~k², thinning density, unstructured words); only Knight's own
   `2^(k−2)` locus on mechanical words is uniform.  **Thread 2 re-priced ~12% → ~5%.**
   Commit `d9ef876`.  Full write-up: `FRONT-B-ROUTES.md` §2026-08-23 (both sections).
3. Not pulled (deliberately left): the compression attack itself (hard open math, wants
   fresh eyes), Front A route map (`FRONT-A-ROUTES.md`, absorbed but unworked),
   `PI02-SKETCH.md`, and two cheap curiosities - Lean-ing the negative-drift argument,
   and the census's bonus datum *"distinct rotations of a primitive word have distinct
   numerators"* (provable: a repeated member value closes the orbit early, contradicting
   primitivity - a pleasant-lemma candidate for `Powers.lean`).

## Next attack

- **The sharpened Route-2 target**: `frontB_of_compression_le_91` reduces Front B to
  *"a primitive nontrivial integral cycle has ≤ 91 circuits"* - one statement, no ladder
  extrapolation.  Nothing formal exists toward proving compression itself; the prose map
  (`FRONT-B-ROUTES.md`) stands, with the new doctrinal note that compression must be
  sign-blind (positivity lives in the ladder).
- Alternative threads: `BoundedDen` on primitive words (**~5% after the census** - a new
  family needs new combinatorial input), Front A route map (`FRONT-A-ROUTES.md`),
  `PI02-SKETCH.md`.
