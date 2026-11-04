# HANDOFF 2026-11-04 — the stage word law (`wip/orbit-word-law`)

Kickoff: `KICKOFF-2026-11-04-stage-word-law.md`.  Gate: `sorry-free:CollatzMoonshot/Conjugacy/OrbitStageLaw.lean`.
Frozen: `StageWordLaw`, `BadStart`, `WindowMatch`, `normal_iff_le_four`, and the statement of
`stageWordLaw_of_le_four` (unchanged).

## State: DONE

`OrbitStageLaw.lean` is sorry-free.  `#print axioms normal_iff_le_four` (from `/tmp`, with a `sorry`
control that printed `sorryAx`) gives `propext, Classical.choice, Quot.sound`; so do
`stageWordLaw_of_le_four` and `not_badStart_of_chain'`.  `lake build CollatzMoonshot` green (8952 jobs).
Frozen statements unchanged (the diff on `OrbitStageLaw.lean` is one import, the body of
`not_badStart_of_chain`, and two docstrings).

| leaf | status |
|---|---|
| `expSparse_not_goodZero` (P1) | proved (`OrbitStageLawWords.lean`) |
| `sufTail_holds`, `oddTail_holds` (Chernoff) | proved (`OrbitStageLawTerras.lean`) |
| `expSparse_preimage_stageMap` (P2, pullback) | proved (`OrbitStageLawPull.lean`) |
| `not_badStart_of_chain` (P3/P4) | **proved** (`not_badStart_of_chain'`, `OrbitStageLawChain.lean`) |
| `expSparse_biUnion_range`, `tendsto_stage_of_expSparse` | proved (`OrbitStageLawRate.lean`) |

## The chain (`OrbitStageLawChain.lean`)

* `abs_wdev_le_of_classGood`: `ClassGood u η s r` ⇒ every prefix of `≤ s` letters deviates by
  `≤ |u| η s + 2|u|` (classes mod `|u|` via `wcnt_mul_eq_sum_blkCnt`).
* `size_stageMap_ge`: `OddLow (1/200)` ⇒ `size (stageMap M) ≥ (39/50) size M − 1`.
* `size_stageMap_le`: `SufGood (s/10)`, `s ≥ 70` ⇒ `size (stageMap M) ≤ size M`.
* `iterate_chainLen`, `abs_wdev_chain`, `chain_sizes`, `chainLen_ge`: twelve windows cover
  `4.3 k − 60` letters, each deviating by `≤ |u| η k + 2|u|`.
* `not_badStart_of_chain'`: `η = δ / (48|u|)`, `γ = 1/200`, `J = 12`, `k₀ = max 1200 (⌈50|u|/δ⌉ + |u|)`;
  `u = []` and `C = 0` separately.  No step was structural.

Nothing remains in the gated scope.

## Checkpoint (final, run stopped)

Branch `wip/orbit-word-law`; proof HEAD `e9ed727`, handoff commits after it.  Working tree clean apart
from untracked `CLAUDE.local.md`.  `box done --green` signalled; the host re-verifies the build.

Next (needs an operator kickoff; nothing is owed in this scope): `logNormal_of_orbitWordLaw` in
`ChampernowneLog.lean` (see the orbit-word-law handoff), or tightening the chain to the kickoff's
`J = 9` at `θ = log₂ √3`, which is cosmetic.  Other `src/` sorries are designated-open.
