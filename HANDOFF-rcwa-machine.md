# HANDOFF: RcwaMachine (Theorem C machine core)

Kickoff: `KICKOFF-2026-10-16-rcwa-machine.md`.  Target: close every `sorry` in
`CollatzMoonshot/RcwaMachine.lean` without changing ratified statements.

## Done
- Lemma M, abstract: `visits_boundary_forward` (pigeonhole `Finite.exists_infinite_fiber` +
  `Nat.nth` enumeration + `wellQuasiOrdered_le`, packaged as `exists_lt_fst_eq_snd_le`),
  `visits_boundary_backward` (forward theorem for `flip Step`, via `offRun_reverse`,
  `lapNotUp_flip`), `immortal_iff_macro` (→ enumerate B-visits with `Nat.nth`, `Nat.nth_count`
  for "no visit in between"; ← concatenate witnesses with a stage counter `nxt^[t] (0,0)`),
  `reverse_immortal_iff_macro` (from the forward one for `flip Step`, `macroStep_flip`).
- `TwoCounter.visits_boundary`: `lap_mixed` telescopes the lap vector.

- `completeFun_bijective` (direct injective/surjective via `completeFun_cases`).
- `sameCycle_succ_of_not_diverges`, `not_sameCycle_of_cut`.  The latter rests on the leg
  invariant `OnLeg` / `onLeg_step` / `reach_le`: forward `σ`-orbits visit line positions only
  upward and never past a cut.  Only (H2) is used, so (H1) is an unused binder there (linter
  warning; the ratified statement keeps it).

- `card_orbits`: anchors `exists_sameCycle_lineEmb` (H1 splices two infinite chains into a
  bi-infinite orbit otherwise); divergent sources inject into `Orbits` (`not_sameCycle_of_cut`);
  the complement of that range is a subsingleton (`hup`: a cut-free orbit swallows every line
  position above it), nonempty when the cuts are finite (positions above the last cut), absorbed
  by `ℵ₀` arithmetic when infinite.  `Cardinal.mk_sum_compl` assembles `1 + #D`.
- `sameCycle_all_iff` (direct, via `sameCycle_of_noCut`), `infinite_orbits_iff` (from
  `card_orbits`), `one_or_infinite_orbits` (case split).

## Status
Every `sorry` in `RcwaMachine.lean` is closed.  `#print axioms` on all twelve ratified
theorems: `[propext, Classical.choice, Quot.sound]`.  Ratified statements unchanged since
`f6b2832` (checked by diff: only `sorry` lines removed).  Lines ≤ 100 characters.

## Open
- Nothing in this file.  Cosmetic: `Int.le_induction` deprecation warnings, unused `h1` in
  `not_sameCycle_of_cut` (kept, ratified signature).
