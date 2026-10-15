# HANDOFF — amusical-swap (2026-10-14)

**Objective COMPLETE.** `CollatzMoonshot/AmusicalSwap.lean` is sorry-free; `ampSwap` and the six
ratified statements are unchanged (diff removes only `sorry` lines).

* `ampSwap_bijective`: explicit two-sided inverse `g` (`3m ↦ 2m`; `3n+1 ↦ 4n+1 / 4n+3`;
  `3n+2 ↦ 4n+3 / 4n+1` by `c n`), via per-residue evaluation lemmas `e0 e1 e3 g0 g1 g2`,
  then `cases c n`.
* `ampSwap_even`, `ampSwap_offset` (`abs_le`, offsets `±1, ±5`), `ampSwap_false`: unfold,
  `split_ifs`, `push_cast`, `omega`.
* `nc_iff_pse_parent`: (←) `Nat.find` on the least `k ≥ 1` with `x (s+k) ≤ x s + D`.
  Injectivity `hx` is not needed (kept in the ratified statement; referenced by `have _ := hx`).
* `next_survivor_le`: `hfut 1` and `omega`.

Axioms: all six use only `propext`, `Quot.sound` (and `Classical.choice` for the bijection and
CT1).  No `native_decide`.  `lake build CollatzMoonshot.AmusicalSwap` green (8707 jobs).

Next: nothing open in this objective's scope.

## Checkpoint

* Branch `wip/amusical-swap`, proof commit `6fd5068` (stacked on `wip/amusical-squares`).
* Stop signalled via `box done --green`; the scoped target `sorry-free:CollatzMoonshot/AmusicalSwap.lean`
  is met.  Remaining `sorry`s elsewhere in `src/` are designated-open for this run.
* `DIRECTION.md` CURRENT DIRECTIVE (awaiting a new idea) still stands; no follow-on proof lap
  is selected.  Next step, if any, is the operator's: merge/stack this branch.
