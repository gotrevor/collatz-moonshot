# HANDOFF: cm-format-lower (kickoff `KICKOFF-2026-10-16-cm-format-lower.md`)

## Progress log

- **`CounterMachine.lean`: all 11 lemmas proved** (sorry-free).  Helpers added: `CM.StepsN`
  (counted steps), `StepsN.of_reaches`, `StepsN.of_transGen` (under `Det`, a run to a stuck
  configuration passes every configuration on any run from its start, with fewer steps left; the
  measure for the (→) half of `halts_iff_of_sim`), and the private `lift`/`step_lift_iff`/
  `step_lift_dst` for `halts_restrict`.
- **`CounterMachineUniversal` §1-§2 proved** (`f0fa3da`): `exists_universal`,
  `not_computable_universal`, `undigit_num`, `num_div_five`, `num_cons`, `stackVec_init`,
  `computable_inputNum` (helper `inputNum_pos`; recurrence `I 0 = 2`, `I n = 3 + n%2 + 5 I(n/2)`
  by cases on `(n : Num)`, then `Primrec.nat_strong_rec`).
- **Next:** §3 `det_lcm`, `normalAt_lcm`; §4 `stepAux_reaches`, `stuck_halt`, `halts_iff_eval`;
  §5 `reachSet_finite`, `reachSet_closed`, `undecidableCM`.
- **§3 + `stuck_halt` proved.**  Route: `gadget_eq : gadget s v = (gadA s v).map (emb s v)`, where
  `gadA` is an abstract rule list over the two counters (`Option Unit`) with phase sources
  (`ARule`), so determinism is `decide` on closed lists (`pushA_det`, `popA_det`, `peekA_det`)
  and transfers through the source-injective `emb` (`embSrc_inj`, `mem_gadget`).
  `mem_gadget` is the tool for every "which rule is this" question (also §5 closure).
