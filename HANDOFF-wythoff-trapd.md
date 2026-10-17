# HANDOFF: wythoff-trapd (degree-d trap identity, `WythoffTrapDegree.lean`)

Kickoff: `KICKOFF-2026-10-16-wythoff-trapd.md`.  Build: `lake build CollatzMoonshot.WythoffTrapDegree`.

## Status (2026-10-17)

* §1 synthetic division: `quotCoeff_rec`, `mul_quotCoeff_zero`, `phase_identity`,
  `sub_mul_sum_quotCoeff` — **proved**.  `sub_mul_sum_quotCoeff` was moved (statement unchanged)
  to just after `phase_identity`, since its proof is `phase_identity` at `v i = tⁱ`.
* §2 identity and trap: `wy_iterate_eq_floor`, `wy_iterate_eq_of_trap`, `trapSetD_trap`,
  `wy_iterate_add_of_mem_trapSetD`, `wy_iterate_two_eq_floor` (from `wy_iterate_eq_floor`, as
  required) — **proved**.  Helpers: `wy_iterate_sub_eq`, `trapSetD_iterate`.
  So the cubic identity `wy_iterate_three_cubic` and trap `cubicSet_trap` are unconditional
  and axiom-clean (`propext, Classical.choice, Quot.sound`).
* `wy_iterate_eq_of_trap` avoids the `sup'` of the paper proof: with `S = Σ(−q_i) ≤ 1`,
  `X = S − Σ(−q_i)(1 − f_i)`; if `S < 1` done, if `S = 1` some `−q_i > 0` makes the gap sum
  strictly positive (`Finset.sum_pos'`).
* §3 `trapSetD_entry_infinite` — open (the only `sorry`).

## Update (2026-10-17, later): file sorry-free

* §3 `trapSetD_entry_infinite` **proved** (conditional only on the `WeylEquidistributionMulti`
  hypothesis, as ratified).  `#print axioms` of it, of
  `wyPerm_infinitelyManyInfiniteOrbits_of_trapD` and `cubicPerm_infinitelyManyInfiniteOrbits`:
  `propext, Classical.choice, Quot.sound`.
* Helpers (section `Entry`): `wy_iterate_two_mul_floor` (box phases ⇒ `Wⁱ(2k) = 2⌊kAⁱ⌋`),
  `boxLow`/`trapBox` (box `Π[L_j, L_j + η)`, `L_{j+1} = A(L_j + η)`), measurability, null
  frontier (`closure \ interior ⊆ Icc \ pi Ioo`, equal volumes), volume `η^d`; growth
  (`growth_iterate`), `eq_of_iterate`, `exists_seed`, `exists_window` (count on
  `(LN, (L+1)N]` → ∞ from the Cesàro limit).
* Route deviates from the kickoff's `O(log X)` count: a window of ratio `(L+1)/L ≤ (A+1)/2`
  holds at most one point per seed, so pigeonhole is immediate (as in `coneEntry_infinite`).
* No ratified statement changed (diff vs `9971fac`: only proof bodies, status tags, and the
  verbatim move of `sub_mul_sum_quotCoeff` below `phase_identity`).
