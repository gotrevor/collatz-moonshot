# HANDOFF 2026-11-04 — the time law (`wip/orbit-word-law`)

Kickoff: `KICKOFF-2026-11-04-time-law.md`.  Gate: `sorry-free:CollatzMoonshot/Conjugacy/OrbitTimeLaw.lean`.

## TARGET MET

Both frozen targets are proved; statements byte-identical to the planting commit `09a4012`
(docstrings only changed).

    #print axioms timeLaw_upper   -- [propext, Classical.choice, Quot.sound]
    #print axioms timeLaw_lower   -- [propext, Classical.choice, Quot.sound]

Checked from `/tmp/AxTL.lean` with a `sorry` control (`sorryControl` shows `sorryAx`).
`lake build CollatzMoonshot` green (8945 jobs).  No `native_decide`, `axiom` or `maxHeartbeats`.
No existing file edited apart from `OrbitTimeLaw.lean`.

## What carried it

1. `timeLaw_lower`: `firstPassage_sharp` at `θ = min (1/2) (βε/2)`, tolerance `ε/2`; `f n > n^θ`
   is a bounded set.
2. `timeLaw_upper` = `timeLaw_odd_window` + odd parts + even reduction.  The even reduction needs
   no 2-adic summability: `2^a m` spends `a ≤ (1/β + ε) a` steps halving.  Target for the odd part is
   a minorant `g m = ⨅_(n ≥ m) f n` (`exists_minorant`).
3. `timeLaw_odd_window`: for each `X`, `P ≤ P(¬GoodOddUpTo δ τ) + M log(X)^(−κ)`, with `J` the
   last scale above `X` (`exists_last_scale`), `x_J ≤ X^α ≤ g m` eventually.
4. **Rates exist; no non-uniform constant.**  `OrbitTimeLawRate.lean`: `winGood_prob_le_rate`
   (`O(1/log x)`, from the bound inside `winGoodWhp_holds`, copied as
   `winGood_prob_eventually_le`), `dTV_chain_le` (`∑_(i<j) C_stab log(x_(i+1))^(−c_stab)`),
   `stage_prob_le`, `κ = min c_stab 1`, `log(x_j)^(−κ) = (α^κ)^j log(x)^(−κ)` (`log_scale_rpow`),
   `chainFail_prob_le_holds` with `M = (C + C_stab G) G`, `G = α^κ/(α^κ − 1)`.  Every threshold
   depends only on `η = 1/1000`.
5. **The time.**  `OrbitTimeLawChain.lean`: `θ = min (1/4) (ε/60)`, `τ = (1 − θ/2)/β`, `δ = θ/16`.
   Height line to `T^(t₁) m ≤ 2^(θ s)` (`tstep_floor_le_of_goodOddUpTo`); run of halvings `d` with
   `2^d ≤ T^(t₁) m` (`ltime_le_add_run`); `j₀` the first `j` with `j = J` or `x_(j+1) < 2^(θ s)`;
   stages `j₀..J` cost `≤ (1001/20) log₂ x_(j₀) ≤ 51 θ s` (`passChain`, `ltime_le_add_sum`,
   `sum_lam_Ico_le`).  Total `≤ (τ + 52θ) s ≤ (1/β + ε) s`.

## Files

- `CollatzMoonshot/Conjugacy/OrbitTimeLaw.lean`: targets, leaves, assembly; 0 `sorry`.
- `CollatzMoonshot/Conjugacy/OrbitTimeLawChain.lean` (new), `OrbitTimeLawRate.lean` (new).

## Next (operator's call)

- `docs/notes/` write-up: total stopping time `(1/β + o(1)) size n` to below any `f → ∞`, in log density.
- Numbers: `experiments/conjugacy/time_law.py` was not re-run this lap.

## Final checkpoint (treadmill stop)

Branch `wip/orbit-word-law`, HEAD `3896b94` + this commit.  Working tree clean apart from the
untracked `CLAUDE.local.md`.  `box done --green` written; scoped gate at 0.  No Aristotle job.
Exact next steps, for whichever operator kickoff comes next:
1. Re-verify: `lake build CollatzMoonshot.Conjugacy.OrbitTimeLaw`, then `#print axioms timeLaw_upper`
   and `timeLaw_lower` (expect `propext, Classical.choice, Quot.sound`).
2. Optional: re-run `experiments/conjugacy/time_law.py` against the proved constant `1/β`.
3. Optional: `docs/notes/` note on the time law, pinned at this commit.
