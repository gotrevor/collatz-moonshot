# HANDOFF: stopped prefixes, RT-low (ncentropy, research §40)

- Branch: `wip/amusical-ncentropy`.  Kickoff: `KICKOFF-2026-10-14-amusical-ncentropy.md`.
- Target file `CollatzMoonshot/AmusicalNearCycleEntropy.lean`: 0 sorries.  `trueRuns`,
  `boolListsUpTo`, `stoppedPrefixes` and the five statements unchanged (only import lines and proof
  bodies changed).  `RhinBound` is not used.  No `native_decide`, no axioms, no large `decide`.
- All five (`nearCycleAt_prefix_balance`, `sum_stoppedPrefixes_le`, `card_stoppedPrefixes_le`,
  `sum_choose_le_exp_binEntropy`, `ncard_deep_lowRun_le`) depend only on
  `[propext, Classical.choice, Quot.sound]`.  Full `lake build` green.

## How

Helpers in `CollatzMoonshot/AmusicalNearCycleEntropy/*.lean`.

- **Chernoff** (`Chernoff.lean`): as in the kickoff; `exp(n H(j/n)) = (α^j (1−α)^{n−j})⁻¹`.
- **NB, count** (`Prefixes.lean`): `runs`/`upTo`/`SP` are verbatim copies of the ratified defs
  (the main file identifies them by `funext`+induction).  `SP_succ_subset`: a stopped prefix with
  `τ + 1 ≥ 2` `E`'s is `E :: s'` (`s' ∈ SP τ k M`) or `E O^{c+1} ++ s'` (`s' ∈ SP τ (k−1) (M−1−c)`).
  Induction on `τ`; Pascal (`sum_choose_succ`), geometric sum for NB, reflected hockey stick for
  the count.
- **P2′** (`Balance.lean`): `carry_potential_at` is MR I's potential with the scale `x 0` replaced
  by any threshold `P` below the later points; `P = p + D`.  Deviation: `prefix_balance'` needs
  only `x_t` even (the `hO` hypothesis is unused, since `cntR (t+1) ≤ eRuns p t + 1` always).
- **RT-low** (`Word.lean`, `Stopped.lean`, `Estimates.lean`, `RTLow.lean`).  Deviations from the
  kickoff sketch, all simplifications:
  * no dyadic blocks: one residue-class count over `[0, ⌊D L^14⌋]` (`card_fiber_le`), so no
    `L` factor on the tail term;
  * no binary entropy: `Σ_{i<m} C(n, i) ≤ 9^m (10/9)^n` (binomial theorem at `α = 1/10`), which is
    the exact Chernoff exponent at `m/τ = 1/10`;
  * the main exponent is `347/400 + 1/400` (`100 log 5 + 53 log 2 ≤ 90 log 9`; `L^14 ≤ K D^{1/400}`
    via `log L ≤ log(5600/log 2) + log D / 5600`); the tail is about `0.60`;
  * `τ = ⌈L/4⌉`, `m = ⌊L/40⌋`, `M = ⌊141 τ/100⌋ + 4` (`B < 1.41 τ + 2.59` from P2′ with
    `100 log(3/2) ≤ 141 log(4/3)`, `log(4/3) ≥ 1/4`); `L < 1000` goes into the constant
    (`2^1000 · 1000^14 + 1`).
  Numerical inputs are integer-power comparisons by `norm_num`
  (`set_option exponentiation.threshold 400` for `2^348`, `2^317`).
  The branch word is `key` (`0`/`1`/`3` = `E`/`x ≡ 1`/`x ≡ 3`); `key_dvd`: equal words of weight
  `w` force `2^w ∣ x − y`.

## Next steps

Nothing owed on this kickoff.  The host merges `wip/amusical-ncentropy`.
