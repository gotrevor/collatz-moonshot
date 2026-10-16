# HANDOFF: orbit-count (KICKOFF-2026-10-16-orbit-count.md)

Branch `wip/orbit-count`.  Target: every `sorry` in `CollatzMoonshot/RcwaOrbitCount.lean`.

## Done (all ratified statements unchanged; only the 29 `sorry` lines removed vs `8885e9f`)

Headline axioms (`exists_table_iff_mortal`, `exists_valid_machine_mortal`, `tableOf_orbits`,
`not_computable_oneOrbit`, `not_computable_finiteOrbits`, `orbit_count_family`,
`oneOrbit_not_re`, `oneOrbit_not_coRE`, `mortalityUndecidable_of_totalityFamily`, `total_*`):
`propext, Classical.choice, Quot.sound`.

- §2 helpers: `lapNotUp_of_lapsMixed` mirrors `lapNotDown_of_lapsMixed` with the negative lap
  entry; `exists_forever_of_not_halts` and `exists_source_reaches` iterate a `choose`n successor
  (predecessor) on the subtype `{d // ¬ Halts d}` (`{d // Reaches d c}`);
  `halts_of_reaches` by `ReflTransGen` tail induction and `cases_head`.
- §1: `card_orbits_complete` is `Cardinal.mk_congr (Quotient.congr (Equiv.sumEmpty ℤ Empty) _)`
  with `Good.sameCycle_iff`.  `infinite_divergent` uses junk `m k = 1 + 6·5^j·k`; the unit
  condition is `(5 : ZMod (5^j))^j = 0` via `ZMod.natCast_self`; injectivity from
  `(junk _).2.2`.  `card_orbits_sigma_eq_aleph0_iff` upper bound: `Orbits` is a quotient of `ℤ`.
- §3: `computable_tableOf` = `fst ∘ computable_reduce ∘ (id, const (0,0,0))`, `.of_eq rfl`.
- §4: helper `exists_index` (s-m-n from `exists_code` + `curry` + `eval_curry`), and
  `computablePred_comp` / `rePred_comp` (pullback along a computable map).  `total_not_re` uses
  `cond (evaln x c 0).isSome none (some 0)`; `total_not_coRE` uses `eval c 0`.
- Mortality transfer: `histWrap_macro_sound` is the first half of `histWrap_macro_hist` plus
  `macroStep_functional`.  `histWrap_mortal_iff` / `godel_mortal_iff` (←): `exists_macro_chain`,
  `choose` the per-step decodings, glue with `HState.bnd.inj` (resp. `GState.ent.injEq` +
  `genc_inj`), then `CM.not_halts_of_forever`.  `double_sourcesHalt_iff` as in the kickoff.
- `exists_valid_machine_mortal` copies `exists_valid_machine`'s construction verbatim and chains
  the three `↔`.

## Environment note

`lake env lean` intermittently failed with "Too many open files" (a host/mount limit, not the
container's `ulimit`); retrying after ~20 s always worked.

## Next

Nothing owed on this kickoff.  The later layer (discharging `TotalityFamily`, or the cheaper
`MortalityUndecidable` alone) is described at the end of the kickoff and is a new campaign.
