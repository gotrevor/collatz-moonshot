# HANDOFF amusical-notnormal (research §54)

Branch `wip/amusical-normal`.  Kickoff: `KICKOFF-2026-10-15-amusical-notnormal.md`.

## Done
* `CollatzMoonshot/AmusicalNotNormal.lean`: ratified `not_tendsto_evenFrequency_third` proved,
  statement unchanged; `#print axioms`: `propext, Classical.choice, Quot.sound`.  No
  `native_decide`; lines ≤ 100 chars.  Import changed from `AmusicalEscape` to
  `AmusicalCycleBound` (which imports `AmusicalEscape`) to reuse Theorem A★.
* Helpers (all proved): `evenStepCount` (the name `evenCount` was already taken),
  `evenStepCount_mul_period`, `sum_stepBits_add_evenStepCount`,
  `three_mul_evenStepCount_of_tendsto`.

## Route actually taken (simpler than the kickoff's cycle-product sketch)
1. Frequency `→ 1/3 < 2 − log₂ 3` ⇒ periodic, period `p ≥ 1` (`periodic_of_evenFrequency_lt`).
2. Along `k = q p` the frequency is constantly `E/p`; uniqueness of limits ⇒ `3E = p`.
3. If all `U^j m ≥ 4` (`j < p`): `amusical_cycle_min_bound` with lower bound 4 gives
   `2^e 12^k ≤ 3^p 13^k`, `e = 5E`, `k = 2E`, `p = 3E`, i.e. `4608^E ≤ 4563^E`, false.
   (A minimum-over-the-whole-cycle bound suffices; no need to isolate odd elements ≥ 5.)
4. Else some `U^j m ∈ [0,4)`; `nonneg_of_iterate_lt_four` (backward invariance) ⇒ `m ∈ {1,2,3}`;
   apply step 2 with the explicit period (1, 2, 2) and `decide`.

## Next steps
* Host: push `wip/amusical-normal` and merge.
