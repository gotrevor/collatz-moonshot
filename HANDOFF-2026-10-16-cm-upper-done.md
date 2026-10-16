# HANDOFF 2026-10-16: cm-upper done

Branch `wip/cm-upper`, HEAD `24ca5cf` (green, `lake build CollatzMoonshot.RcwaHalting`).
Kickoff `KICKOFF-2026-10-16-cm-upper.md`; running notes `HANDOFF-cm-upper.md`.

## Done
`CollatzMoonshot/RcwaHalting.lean` is sorry-free.  All ratified statements are unchanged
(headers diffed against `664aa67`).  Chain: `histWrap` (Lemma H) → `godel` (Lemma G) →
`double` (Lemma D) → `exists_valid_machine` → `haltingUndecidable_of_undecidableCM` →
`haltingUndecidable`, `not_computable_sameCycle'`.

`#print axioms not_computable_sameCycle'` = `[propext, sorryAx, Classical.choice, Quot.sound]`.
The `sorryAx` comes only from the upstream statements in `CounterMachine.lean` (11) and
`CounterMachineUniversal.lean` (15), which are owned by `KICKOFF-2026-10-16-cm-format-lower.md`.
`RcwaSameOrbit`, `RcwaMachine` and `RcwaHalting` have 0 sorries.

## Next
1. Once the cm-format-lower branch lands, merge it with this one.  Then re-run
   `#print axioms CollatzMoonshot.RcwaHalting.not_computable_sameCycle'`, which should be
   axiom-clean (no `sorryAx`).
2. Open a PR for `wip/cm-upper` (the host pushes).  Scratch files are in `tmp/cmu/` (not
   needed).
