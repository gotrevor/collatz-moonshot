# HANDOFF: cm-format-lower (kickoff `KICKOFF-2026-10-16-cm-format-lower.md`)

## Progress log

- **`CounterMachine.lean`: all 11 lemmas proved** (sorry-free).  Helpers added: `CM.StepsN`
  (counted steps), `StepsN.of_reaches`, `StepsN.of_transGen` (under `Det`, a run to a stuck
  configuration passes every configuration on any run from its start, with fewer steps left; the
  measure for the (→) half of `halts_iff_of_sim`), and the private `lift`/`step_lift_iff`/
  `step_lift_dst` for `halts_restrict`.
