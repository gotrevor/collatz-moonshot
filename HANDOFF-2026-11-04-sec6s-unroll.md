# HANDOFF 2026-11-04: SEC6S lap 1c - the unrolled slice telescope (gate met)

Branch `wip/beyond-words-stretch`, worktree `~/src/collatz-moonshot-stretch`.  Kickoff
`KICKOFF-2026-11-04-sec6s-unroll.md`.

## What landed

`CollatzMoonshot/Conjugacy/SliceTelescopeUnroll.lean`, sorry-free, added to root `CollatzMoonshot.lean`
(root `lake build CollatzMoonshot` green).

* `levelOsc_le_unrolled` (frozen, unchanged): for `m < a`,
  `levelOsc j a m ≤ levelOsc j a (a−1) + Σ_{k ∈ Ico (m+1) a} Σ_{j' < j} C(j−j'−1, a−k−1) · levelOsc j' k (k−1)`.
  `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
* `sum_range_sum_range_choose` (new helper): `Σ_{i<j} Σ_{j'<i} C(i−j'−1, r) y_{j'} = Σ_{j'<j} C(j−j'−1, r+1) y_{j'}`.

Proof route differs from the kickoff's sketch at step 4: instead of the dependent-index swap plus
hockey stick, the layer collapse is the helper above, proved by induction on `j` with
`Nat.choose_succ_succ` (this sidesteps the truncated-subtraction trap entirely: the inner range stays
`range i`).  The `Icc 1 j` sum is reindexed to `range j` via `Finset.sum_Ico_eq_sum_range`.  Main
theorem: `Nat.le_induction` on `a` from `m + 1`, generalizing `j`.

## Owed (SEC6S-PLAN §4 lap 2)

* `sliceMixture_offBand_le` (hypergeometric tail leaf) — the remaining named leaf of target 2.
  Route per plan: Bernoulli(1/2) bit representation over all `r < 2^j`, higher moments / Chernoff.
* Frozen SEC6S targets in `SliceOscCentral.lean` untouched.

## Final checkpoint

HEAD at checkpoint: `5bd335f` on `wip/beyond-words-stretch` (not pushed; host pushes).  Scoped target
`sorry-free:CollatzMoonshot/Conjugacy/SliceTelescopeUnroll.lean` met; `box done --green` signalled.

Exact next step for the next run: SEC6S-PLAN §4 lap 2, prove `sliceMixture_offBand_le` (the remaining
leaf of SEC6S target 2) via the Bernoulli(1/2) bit representation over `r < 2^j` with higher moments
or a Chernoff bound, mirroring `sum_oddDeviation_sq`.  A fresh kickoff should freeze that leaf first.
