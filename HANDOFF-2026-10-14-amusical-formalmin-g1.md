# HANDOFF 2026-10-14: amusical-formalmin, Proposition G1 proved (run finished)

- **Branch:** `wip/amusical-formalmin`.  **HEAD:** `9b5a862` (before this doc's commit).
- **Done:** the scoped target `CollatzMoonshot/AmusicalFormalMin.lean` is sorry-free.
  - `coarse_quasiInvariant_bounded` (Proposition G1) is proved via the two-visit lemma
    `TwoVisit.exists_two_visit` in `CollatzMoonshot/AmusicalFormalMin/TwoVisit.lean`.
  - `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
  - Real `lake build CollatzMoonshot.AmusicalFormalMin` is green; the pre-commit hook re-ran it.
  - `box done --green` has been signalled.
- **Detail:** see `HANDOFF-amusical-formalmin.md` for the proof route, helper list, and the
  `/tmp/ll` native-fs workaround for the host's "Too many open files" loader failures.
- **Next steps (optional, new scope):** Proposition G2 (growing modulus).  It needs a connector
  of length `O(log M)` in place of the factorial-length fixed connector.  No work has started.
