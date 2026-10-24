# Handoff: Bridge3 edges

Branch `ren/bridge3-edges` (worktree `~/src/collatz-moonshot/worktrees/bridge3-edges`), cut from
`ren/conjugacy-ladder` at daad7a1.  Operator plan: `BRIDGE3-NEXT.md`.  Scoped completion target:
`sorry-free:CollatzMoonshot/Conjugacy/Bridge3.lean`.

## Checkpoint (2026-10-24, lap 0, by the attended session personal-c5)

The statements, definitions and teeth are in place and build green, with three sorries:
`bias_eq_sum_levelSign`, `abs_levelSign_le` and `biasDecays_of_truncatedSyracMixing`.  The
mathematics is research note §11.  The numerical checks are `experiments/conjugacy/fsm_bridge.py`
(the reduction holds exactly for `j ≤ 20`) and `twisted_charfn.py`.

Next: edge 2 (elementary, self-contained), then edge 1, then edge 3.
