# HANDOFF 2026-10-06: record constant 0.1228 proved

Kickoff: `KICKOFF-2026-10-06-record-constant.md`.

## Phase 1 (done)
`exists_farFromIntegers_1228` depends only on `propext`, `Classical.choice`, `Quot.sound`.
Certificate: `P1228` (the eleven closed intervals of `arc_cert_beta_1228_vw_k0.json`),
`relaxedStrategy_1228`.  Every one of the 22 (interval, d) cells uses the clamp `u = max a c`
with the arc lift `k = 0` and a single target interval; generic cell lemma `cell1228`, all side
conditions by `norm_num`.  No cell failed; the constant was not shrunk.

## Phase 2 (done)
- `mahler_barrier`: moved after `relaxed_barrier_13_20`, one-line corollary.
- `relaxedStrategy_near_afs`: `relaxedStrategy_afs_closed.mono` (new `RelaxedStrategy.mono`);
  moved after `relaxedStrategy_afs_closed` together with `trapsResidueClass_near_afs`.

## Phase 3 (next)
`relaxed_barrier` (7/57).  See its docstring and `experiments/arc_barrier.py`.  Plan: define the
component game step on closed windows, prove domination, then the runaway lemma
(`g x = 27x/8 - 5/4`), then transcribe the 13-move funnel.

## Phase 3 (done, same day)
`relaxed_barrier` and `not_relaxedStrategy_13_100` are proved (standard axioms only).
- `BarrierGood P l x y`: some strategy window fits in `[x, y]`.  `barrier_step` is the domination
  step; the relative parity `d` is free because the absolute parity is `fract(3m/2 + d)`.
- Monotonicity in `β` means only one β-piece is needed: `(7/57, 7126/58025)`.  The adversary tree
  (35 distinct windows, generated from `arc_barrier.py`'s `children`, both root parities) is
  `barrierNode0..34`; clean leaves go to `barrier_runaway` (`barrier_block`, `g x = 27x/8 - 5/4`,
  induction on `(27/8)^n (x - 10/19) ≥ 1`).

All three kickoff phases are complete.  Remaining sorries in ArcTrap.lean are the do-not-touch
list (`E_*`, `1227`, `exists_trapped_of_winningStrategy`, `relaxedStrategy_afs`,
`two_pow_le_card_admissibleWord`).  Exit: `box stuck` (the repo-wide gate cannot see a scoped
completion); next assignment needs an operator kickoff.
