# HANDOFF 2026-10-16: RcwaMachine done

Branch `wip/rcwa-machine`, HEAD `eefd17d` (plus this doc).  Kickoff:
`KICKOFF-2026-10-16-rcwa-machine.md`; scoped target `sorry-free:CollatzMoonshot/RcwaMachine.lean`
is met.  Running notes: `HANDOFF-rcwa-machine.md`.

## Done
- Completion: `completeFun_bijective`, `sameCycle_succ_of_not_diverges`, `not_sameCycle_of_cut`,
  `card_orbits` (`#Orbits = 1 + #divergent sources`), `sameCycle_all_iff`,
  `infinite_orbits_iff`, `one_or_infinite_orbits` (the `{1, ∞}` dichotomy).
- Lemma M: `visits_boundary_forward/backward`, `immortal_iff_macro`,
  `reverse_immortal_iff_macro`, `TwoCounter.visits_boundary`.
- All twelve ratified theorems: `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
  Ratified statements unchanged since `f6b2832` (diff removes only `sorry` lines).

## Next steps
- Host: push `wip/rcwa-machine` and open a PR into `main`.
- Optional cosmetics: `Int.le_induction` → `Int.leInduction`; unused `h1` binder in
  `not_sameCycle_of_cut` is part of the ratified signature, keep it.
- Downstream: wire `one_or_infinite_orbits` + `TwoCounter.visits_boundary` into the Theorem C
  reduction (research §57, `undec-lemma.md` / `undec-r25.md`).
