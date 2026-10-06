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
