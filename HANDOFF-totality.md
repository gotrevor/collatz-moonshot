# HANDOFF: totality family (`RcwaOrbitCount.TotalityFamily` discharged)

Kickoff: `KICKOFF-2026-10-16-totality.md`.  Branch `wip/totality-2`.

## Status (2026-10-16)

| File | Status |
|---|---|
| `RcwaTotalityGlue.lean` | **sorry-free.**  All of §1 and §2 proved. |
| `RcwaTotality.lean` | `exists_lab`, `exists_primeData` proved; the assemblies compile on upstream `sorry`s only. |
| `RcwaTotalityCompile.lean` | in progress (12 leaf `sorry`s at kickoff) |
| `RcwaTotalityRestart.lean` | in progress (16 leaf `sorry`s at kickoff) |

## Notes

* Glue helpers added: `act_inc_update`, `glue_step_plug`, `glue_step_link`, `update_add_add`,
  `chainFirst_bnd`, `chainNext_bnd`, `gpos`, `gpos_le`, `glue_stuck_of_stuck`,
  `histWrap_halts_of_stuck'` (the halting ID located at `bnd s` / `act s`, needed to transfer the
  halting run into the glued wrapper, where only `bnd hole` is not stuck-transferable).
* `glue_chain_reaches_of_inr` was moved above `glue_chain_reaches` (statement unchanged) since the
  latter uses it.
* `glueH_mortal_iff`: (→) `CM.halts_iff_of_sim` with `Sim c b := ∃ h, b = (Sum.map bnd id c.1,
  hcfg c.2 h)`; (←) `exists_macro_chain` + `glue_macroStep_cases` + `histWrap_macro_sound`,
  projecting the macro chain to an infinite run of the glued `U` (states chosen via `choose` from
  boundary membership).
* Fast check loop: `lake env lean CollatzMoonshot/<File>.lean` (~7-15 s against prebuilt oleans).
