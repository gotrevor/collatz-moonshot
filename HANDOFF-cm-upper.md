# HANDOFF cm-upper (RcwaHalting.lean)

Kickoff: `KICKOFF-2026-10-16-cm-upper.md`.  Branch `wip/cm-upper`.

## Status
- §1 Lemma M: done (`wellQuasiOrderedLE_pi` = mathlib `Pi.wellQuasiOrderedLE`; helpers
  `Op.act_delta`, `lapNotDown_of_lapsMixed`).

## Notes
- §4 Doubling: done.  Key helpers: `fires_cases` / `double_step_cases` (every firing is fwd /
  turnaround / bwd), `dcfg_inj`, invariant `DInv` (+ `dInv_run`) used for both `endToStart` and
  `double_halts_iff (→)`.
- Gotcha: `![a, b] 0` inside `decide (0 < _)` leaves a `Nat.decLt 0 (![a,b] 0)` instance after simp
  that no lemma matches; state Fin-2 lemmas over a general `v : Fin 2 → ℕ` instead.
