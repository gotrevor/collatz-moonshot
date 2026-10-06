# KICKOFF 2026-10-06 (evening): prove the 0.1228 record constant

**Lane:** closing proofs for a new result.  **Engine:** Opus/low.  **Launched 2026-10-06 on Trevor's go.**

**Target file:** `CollatzMoonshot/Benchmark/ArcTrap.lean`.  Previous kickoff (`KICKOFF-2026-10-06-arc-edge-proofs.md`) is complete; its rules carry over.

**Headline:** `exists_farFromIntegers_1228`.  Some `ξ > 0` has `‖ξ (3/2)^n‖ ≥ 307/2500` for every `n`, against the published record `5/48 ≈ 0.1042` (Dubickas 2008).  It is done when `#print axioms exists_farFromIntegers_1228` shows no `sorryAx`.

## Phase 1: the headline

Soundness (`exists_trapped_of_relaxedStrategy`) is already proved, so what remains is the finite certificate.  Give a `RelaxedStrategy (307/2500) (943/1250) (123/1000) P` with `P` the eleven intervals of `experiments/arc_cert_beta_1228_vw_k0.json` (denominator `2^24`), then conclude.  For `x ∈ [s, 1 - s]`, `Int.fract x = x`.

- The strategy's move `u` must be a function of `a ∈ P` and `d ∈ {0, 1/2}`.  Expect a clamp, `u = max a c` or `min`, chosen per (interval, `d`) cell, as in `relaxedStrategy_afs`'s docstring.  Read the move off `arc_trap_k.py` (`solve_vw`, `vw_orbit`).  Check each cell with `norm_num`/`linarith` over the rational endpoints.
- Check the certificate's interval convention (closed vs half-open) in the JSON/solver before writing `P`.  `P ⊆ Ico 0 1` is required.
- If a cell genuinely fails at the stated `s`, `l`, or endpoints, stop.  Record the failing cell as a Lean `¬`/witness, and exit `box stuck`.  Do not shrink the constant silently.  A smaller constant still above `5/48` is a fallback only with a recorded reason.

## Phase 2: cheap corollaries

- `mahler_barrier`: immediate from `relaxed_barrier_13_20` (move it after that theorem if needed).
- `relaxedStrategy_near_afs`: monotonicity from `relaxedStrategy_afs_closed` (`l = 1/2`, `P = {0, 1/2}`; the bigger arc's lifts contain the closed arc's lifts).

## Phase 3 (stretch): the 7/57 memoryless barrier

`relaxed_barrier` (then `not_relaxedStrategy_13_100` as a corollary, `13/100 > 7/57`).  The docstring and `experiments/arc_barrier.py` give the exact symbolic funnel and the runaway lemma.  This is a real new result; decompose freely.

## Do not touch

`E_*` (the definition `E` from `3b54347` is Trevor's open question), `exists_farFromIntegers_1227` / `exists_trapped_of_winningStrategy` (superseded), `relaxedStrategy_afs`, and `two_pow_le_card_admissibleWord`.

## Exit

When phases 1–3 are done, or the remaining work is out of scope, exit `box stuck` with the reason: the repo-wide gate cannot see a scoped completion.  Update docstring status lines, the `RESEARCH-2026-10-05-arc-trap-games.md` record section, and write a dated `HANDOFF-2026-10-06-record-*.md` each lap.
