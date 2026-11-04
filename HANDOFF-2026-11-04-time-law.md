# HANDOFF 2026-11-04 — the time law (`wip/orbit-word-law`)

Kickoff: `KICKOFF-2026-11-04-time-law.md`.  Gate: `sorry-free:CollatzMoonshot/Conjugacy/OrbitTimeLaw.lean`.

## State

- `timeLaw_lower`: **proved** (`#print axioms`: propext, Classical.choice, Quot.sound).
  `firstPassage_sharp` at `θ = min (1/2) (β ε / 2)`, `ε/2`; `f n > n^θ` is bounded.
- `timeLaw_upper`: **assembled** from named leaves, all in `OrbitTimeLaw.lean`:
  - `timeLaw_odd_window` (proved): window probability of the odd bad set with target `g` tends to 0.
    For each `X`, `P ≤ P(¬GoodOddUpTo δ τ) + M log(X)^(−κ)`; `x_J ≤ X^α ≤ g m` eventually.
  - even reduction (proved, inside `timeLaw_upper`): `2^a m` costs `a` halvings, absorbed since
    `1/β + ε ≥ 1`; no `summableLargeTwoAdic` needed.  `g` from `exists_minorant` (proved).
  - `exists_last_scale` (proved).
  - **open** `chainFail_prob_le`: the rate.  Plan: rate version of `winGoodWhp_holds`
    (`A/(2 lam x+1) + K 2^(−3 n₀) ≤ C / log x`), `dTV_j ≤ ∑_{i<j} C_stab log(x_(i+1))^(−c_stab)`
    by `dTV_chain_step`, stage `≤ P_(x_j)(¬ScaleGood) + dTV_j` (as `stage_whp`), geometric sums with
    `κ = min c_stab 1`, `log(x_j)^(−κ) = (α^κ)^j log(x)^(−κ)`.  No non-uniform constant found:
    every threshold depends on `η = 1/1000` only.
  - **open** `reach_of_chain`: deterministic.  `θ ≈ ε/60`, `τ = (1 − θ/2)/β`, `δ = θ/16`;
    height line at `t₁ = ⌊τ s⌋` gives `T^(t₁) m ≤ 2^(θ s)`; run of zeros `d` after `t₁` has
    `2^d ≤ T^(t₁) m`; `j₀` = first `j` with `j = J` or `x_(j+1) < 2^(θ s)`; stages `j₀..J` cost
    `≤ ∑ lam x_j ≤ 51 α θ s`.  Chain facts as in `readOff_chain` (`start_passes`, `next_passes`,
    `passes_passLoc`).
