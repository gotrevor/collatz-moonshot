# HANDOFF 2026-11-04 — the stage word law (`wip/orbit-word-law`)

Kickoff: `KICKOFF-2026-11-04-stage-word-law.md`.  Gate: `sorry-free:CollatzMoonshot/Conjugacy/OrbitStageLaw.lean`.
Frozen: `StageWordLaw`, `BadStart`, `WindowMatch`, `normal_iff_le_four`, and the statement of
`stageWordLaw_of_le_four` (unchanged).

## State

`stageWordLaw_of_le_four` is assembled (no sorry in its own body) from leaves in `OrbitStageLaw.lean`:

| leaf | status |
|---|---|
| `expSparse_not_goodZero` (P1: one-window good event fails exp-sparsely) | sorry |
| `sufTail_holds` (Chernoff, suffix odd counts) | sorry |
| `oddTail_holds` (Chernoff, odd count lower tail) | sorry |
| `expSparse_preimage_stageMap` (P2, pullback) | **proved** from the two tails (`expSparse_preimage_of_tails`, `OrbitStageLawPull.lean`) |
| `not_badStart_of_chain` (P3/P4, windows, deterministic) | sorry |
| `expSparse_biUnion_range`, `tendsto_stage_of_expSparse` | proved (`OrbitStageLawRate.lean`) |

Siblings (sorry-free): `OrbitStageLawBasic.lean` (defs: `stageMap`, `ExpSparse`, `blkCnt`, `ClassGood`,
`OddLow`, `SufGood`, `GoodZero`), `OrbitStageLawRate.lean`, `OrbitStageLawPull.lean`.

## Plan for the open leaves

* Engine (new sibling `OrbitStageLawTerras.lean`): block product formula
  `∑_(r<2^(s+L)) G(r) h(T^s r) = (∑_(r<2^s) G)(∑_(x<2^L) h)` for `G` 2^s-periodic, `h` 2^L-periodic
  (lift identity `tstep_iterate_add_mul_two_pow`, `x ↦ b + 3^a x` a bijection mod `2^L`); hence
  `∑_r λ^(blkCnt P L o q r) = 2^(s−qL) 2^o (2^L − c + cλ)^q`; Chernoff with `λ = 1 + η`,
  `log(1+η) ≥ η/(1+η)`: `#{(p+η)q ≤ Y} ≤ 2^s exp(−q η²(1−p)/(1+η))`.
* Tails: `oddCount r (o+q) − oddCount r o = blkCnt odd 1 o q r`; lower tail of odd = upper tail of even.
* `ClassGood` tail: match / non-match counts per class `c < |u|`, union over `q ≥ η s`.
* Chain: `ClassGood ⇒ |wdev u r 0 ℓ| ≤ |u| η s + 2|u|` for `ℓ ≤ s`; `OddLow (1/200)` ⇒
  `size Φ M ≥ (39/50) size M − 1` (via `three_pow_mul_le`, `logb_three_ge`); `SufGood (s/10)` with `s ≥ 70` ⇒
  `size Φ M ≤ size M`; `J = 12` windows, `∑_(j<12) (39/50)^j ≥ 4.3`.
