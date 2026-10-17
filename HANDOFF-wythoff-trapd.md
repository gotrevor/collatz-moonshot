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
