# HANDOFF 2026-11-04 — the stage word law (`wip/orbit-word-law`)

Kickoff: `KICKOFF-2026-11-04-stage-word-law.md`.  Gate: `sorry-free:CollatzMoonshot/Conjugacy/OrbitStageLaw.lean`.
Frozen: `StageWordLaw`, `BadStart`, `WindowMatch`, `normal_iff_le_four`, and the statement of
`stageWordLaw_of_le_four` (unchanged).

## State

`stageWordLaw_of_le_four` is assembled (no sorry in its own body) from leaves in `OrbitStageLaw.lean`:

| leaf | status |
|---|---|
| `expSparse_not_goodZero` (P1) | **proved** (`OrbitStageLawWords.lean`) |
| `sufTail_holds` (Chernoff, suffix odd counts) | **proved** (`OrbitStageLawTerras.lean`) |
| `oddTail_holds` (Chernoff, odd count lower tail) | **proved** |
| `expSparse_preimage_stageMap` (P2, pullback) | **proved** (`expSparse_preimage_of_tails`, `OrbitStageLawPull.lean`) |
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

## Checkpoint (lap end)

Branch `wip/orbit-word-law`, HEAD = this commit.  Working tree clean apart from untracked
`CLAUDE.local.md`.  One `sorry` left in the gated file: `not_badStart_of_chain` (P3/P4).  Everything
else under `stageWordLaw_of_le_four` is proved; `lake build CollatzMoonshot.Conjugacy.OrbitStageLaw` green.

### Exact next steps for `not_badStart_of_chain` (new sibling `OrbitStageLawChain.lean`)

Choose `γ = 1/200`, `J = 12`, `θ' = 39/50`, `η = δ / (4 J |u|)` (case `u = []` separately: `wdev = 0`,
count `= C k`, so never bad).  Lemmas, in order:
1. `ClassGood u η s r → ∀ ℓ ≤ s, |wdev u r 0 ℓ| ≤ |u| η s + 2|u|`: write `ℓ = q|u| + ρ`;
   `wcnt u r 0 (q L) = ∑_(c<L) blkCnt (WindowMatch (uLet u) L 0) L c q r` (positions `jL + c`;
   `WindowMatch g L (c+jL) r ↔ WindowMatch g L 0 (T^(c+jL) r)` by `Function.iterate_add_apply`);
   tail pieces by `abs_wdev_le`, `wdev_add`.  For `ℓ + L − 1 > s` compare with `ℓ₂ = s + 1 − L`.
2. `OddLow γ s M`, `M ≥ 1`, `size M = s` → `(39/50) s − 1 ≤ size (stageMap M)`: `three_pow_mul_le`
   gives `stageMap M ≥ 3^a / 2`; `M < 2^size`; `logb_three_ge : 1.58 ≤ log₂ 3`; `0.495·1.58 ≥ 0.78`.
3. `SufGood (s/10) s M`, `s ≥ 70` → `size (stageMap M) ≤ s`: `two_pow_mul_le` + `sum_offset_le`
   give `stageMap M < 3^a + s 2^(s/10)` with `5a ≤ 3s`; `3^a ≤ 2^(s−1)` for `s ≥ 21` (via
   `three_pow_le_two_pow`-style `(3^a)^5 ≤ 27^s`), `s 2^(s/10) ≤ 2^(s−1)` for `s ≥ 70`.
4. Chain: `M_j = stageMap^[j] m`, `s_j = size M_j`, `t_j = ∑_(i<j) s_i`, `T^(t_j) m = M_j`
   (`Function.iterate_add_apply`, `stageMap` unfold).  Induction: `s_j ≤ k`, `s_j ≥ θ'^j k − 5`.
   `∑_(j<12) (39/50)^j ≥ 4.3` by `norm_num`; so `t_12 ≥ 4.3k − 60 ≥ 4k + L` for large `k`.
5. `|wdev u m 0 ℓ| ≤ j (L η k + 2L)` for `ℓ ≤ t_j` (induction, `wdev_add`, `wdev_shift`).
6. `BadStart` count `= wcnt u m 0 (C k + 1 − L)` for `1 ≤ L ≤ C k`; deviation `≤ |wdev| + L ≤ δ k`.
