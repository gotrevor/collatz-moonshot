# HANDOFF 2026-10-10: tenth exclusion closed

Branch `ren/g2-hunt-flatto-ceiling`, HEAD `bd2d355`.

## Done
- `ArcSolverComputable.no_kRelaxedStrategy_7_57_plus_tenth` (k = 1, 2, 3 at β = 7/57 + 1/10000) PROVED via
  `sweep_7_57_tenth_k1..k3` (`native_decide`, N = 2^20, δ = 1/20001, fuel 600) and `no_kRelaxedStrategy_of_codeSweep`.
  Axioms: propext, Classical.choice, Quot.sound, three native_decide.  Module build 1912 s.
- Sorried copy deleted from `ArcSolverInclusion.lean` (now sorry-free).  `ARC-SOLVER-TENTH-DIRECTION.md` complete.

## Notes
- `ArcDelayGame.lean` was already staged by someone else and is left uncommitted (not this lap's work).
- The module now costs ~32 min to rebuild; consider splitting sweeps into their own file if rebuild cost bites.

## Next
- Possible: push k higher at 7/57 + 1/10000 (Rust is empty only up to k = 3 so far), or tighten β further.
