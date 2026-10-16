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

## Open
- Completion section (bijectivity, orbit lemmas, `card_orbits`, corollaries).
