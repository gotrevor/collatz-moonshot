# HANDOFF: amusical near-cycle (SQ, Sep3 mirror, NC′), DONE

- Branch: `wip/amusical-nearcycle`.  Kickoff: `KICKOFF-2026-10-14-amusical-nearcycle.md`.
- Target file `CollatzMoonshot/AmusicalNearCycle.lean`: 0 sorries.  `NearCycleStart` and the four
  statements unchanged (only the import line, proof bodies and docstrings changed).
- `bwdSurvivor_odd_separation`, `rung_log_ratio`, `rung_depth_spectrum`,
  `infinitelyManyOrbits_of_fwdSurvivor_pos_of_nearCycle_null` all depend only on
  `[propext, Classical.choice, Quot.sound]`.

## How

Helpers in `CollatzMoonshot/AmusicalNearCycle/`, namespace `CollatzMoonshot.Amusical.NearCycle`.

- `Rung.lean`: `iterate_rung` (`Uᵏ p = V^(g−k) n`), `rung_fwd` (`Uᵏ p ≥ n` for `k ≥ 1`),
  `rung_base` (`p ≥ 2`, `p` even, `2n ≤ 3p`, all from `n ≤ U p` by `split_ifs; omega`),
  `abs_log_three_add_sub_le` (`|log(3x+e) − log 3x| ≤ |e|/(3x−1)` via `log y ≤ y − 1` both ways),
  `log_amusical_step`, `rung_log_iter` (induction on `k ≤ g`).  The carry at odd points only needs
  `x ≥ n` (from `hmin`), not the strict `x > n` of the kickoff.
- SQ2 is by contradiction on `fract > θ − 1`, with two integer cases `⌊gθ⌋ − a ≥ 0` / `≤ −1`.
- `Count.lean` (NC′): `IsRungPred n p` (`p < n`, `n = Uᵍ p`, `Uᵏ p ≥ n` for `k ≥ 1`), with
  `exists_isRungPred` (Nat.find on the first backward drop), `IsRungPred.eq` (injectivity),
  `IsRungPred.le` (P′), `IsRungPred.nearCycleStart` (Nat.find on the first re-entry), and
  `card_fwdSurvivor_le`: `#FS ∩ [0,X) ≤ 2r + r⌊X/D⌋ + #NC_D ∩ [0,X)` under `r` orbits.
  **Deviation from the kickoff:** no blocks and no multiplicative telescoping.  On one orbit the
  predecessor is the next lower forward survivor, so gap-`> D` rungs are `D`-separated and
  `Ceiling.card_le_of_sep` gives `X/D + 1` per orbit.  Then `D = ⌈8r/δ⌉ + 1` closes it.

## Observations

- Two ratified hypotheses are unused: `h0` in `bwdSurvivor_odd_separation` and `hg` in
  `rung_log_ratio` (noted in the docstrings).

## Next steps

Nothing is owed on this kickoff.  The host merges `wip/amusical-nearcycle`.
