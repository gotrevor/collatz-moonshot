# HANDOFF: totality family (`RcwaOrbitCount.TotalityFamily` discharged)

Kickoff: `KICKOFF-2026-10-16-totality.md`.  Branch `wip/totality-2`.

## Status (2026-10-16): DONE

All four files are `sorry`-free; `lake build CollatzMoonshot.RcwaTotality` is green.
`totalityFamily`, `mortalityUndecidable`, `mortal_iff_total`, `exists_computable_compile`,
`glueH_mortal_iff` and the five corollaries (`orbit_count_family'`, `oneOrbit_not_re'`,
`oneOrbit_not_coRE'`, `not_computable_oneOrbit'`, `not_computable_finiteOrbits'`) depend only on
`[propext, Classical.choice, Quot.sound]`.  No `native_decide`, no `maxHeartbeats`, no axioms.
No ratified statement changed (one reorder: `glue_chain_reaches_of_inr` above
`glue_chain_reaches`).

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
* Restart garbage flush (`halts_or_reaches_restart`): predicate `GB` (halts or reaches `clr 0`),
  `gb_next` (all successors good ⇒ good; stuck ⇒ halts), then one lemma per state family by
  induction on the drained counter, the input loop `cx` innermost-first (`gb_ad`, `gb_ml₁`,
  `gb_ml`, `gb_mv` under the hypothesis that `cx` is good at the current `x`).
* Restart honest runs (`reaches_round` etc.): drain-loop lemmas `mv_loop`, `ml_loop`, `cw_loop`,
  `bt_loop`, `clr_loop`, `cx_loop`, `clr_all`; macros `upd`, `acf` for counter-function equalities.
* Compile: `godel_map_gen` (one 30-constructor relabelling proof), `pullG`/`roleD` for
  `godel_single_mapQ` without injectivity; `primrec_doubleN` via `Primrec.listFilterMap`.
