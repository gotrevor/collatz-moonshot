# HANDOFF cm-upper (RcwaHalting.lean)

Kickoff: `KICKOFF-2026-10-16-cm-upper.md`.  Branch `wip/cm-upper`.  Scoped objective:
`sorry-free:CollatzMoonshot/RcwaHalting.lean`.  Last commit: `4abc33f` (green).

## Done (all committed, green)
- §1 Lemma M: `wellQuasiOrderedLE_pi` (= mathlib `Pi.wellQuasiOrderedLE`), `revMortal_of_macro`
  (via `lapNotDown_of_lapsMixed`, `Op.act_delta`), `macroStep_transGen`, `macroStep_functional`.
- §4 Doubling: all.  Key: `fires_cases` / `double_step_cases`, `dcfg_inj`, run invariant `DInv`.
- §2 History: all.  `histWrap_lapsMixed` via constant rank (`hrank`) + integer potentials
  (`tF tH wF wH wZ`) + `walk_sum_zero`.  Generic `macroStep_of_chain` (Chain section) builds a
  `MacroStep` from `ReflTransGen` of off-boundary steps.
- §3 so far: `genc_inj`, `godel_macro`, plus helpers `dvd_enc_iff`, `enc_inc`, `enc_dec`,
  `enc_pos`, `gc`, `act_t0/t1/dec0/dec1/inc0/inc1`, `GOff`, `goff_of`, runs `g_transfer`,
  `g_mulChain`, `g_mul`, `g_dvChain`, `g_dv` (with remainder `r`), `g_wChain`, `g_w`,
  `g_rDesc`, `g_r`, `gmacro_of`.

## DONE: `RcwaHalting.lean` is sorry-free (this lap)
- §3 rest: `godel_det`/`godel_rev` (33 / 29 surviving rule pairs; helpers `det_test_counter`,
  `det_test_dst`, `det_nontest`, `rev_test_counter`, `rev_nontest`, `rev_test_src`),
  `godel_normalAt`, `exists_enc` (factorization), `godel_stuck_chain` (the stuck run, three
  cases: no rule / dec at 0 / test with missing branch), generic `not_macro_of_stuck`,
  `godel_halts_of_stuck`, `godel_macro_sound`, `godel_revMortal`, `godel_halts_iff`.
- `godel_lapsMixed`: simpler than the handoff's ℚ-potential plan.  Constant rank `grank`
  (one family per walk); per family one counter only falls (`gdn`), one only rises (`gup`);
  *presence potentials* `gD`, `gI` rise on every rule except a `dec (gdn k)` resp.
  `inc (gup k)`, so `walk_exists` (sum of a closed walk's potential differences is 0) forces
  one of each.  `B.Det` enters only through Prop-`if`s in `gD (b₂)`, `gI (b₂, w₂)`.
- §5: `genc_hcfg_single`, `exists_valid_machine`, `haltingUndecidable_of_undecidableCM`.
- `#print axioms not_computable_sameCycle'`: `sorryAx` only through the upstream statements
  `CounterMachine.lean` / `CounterMachineUniversal.lean` (closed under the parallel
  cm-format-lower kickoff); `godel_lapsMixed` etc. are axiom-clean.

## Infra notes
- Scratch files `tmp/cmu/*.lean` (namespace `CollatzMoonshot.RcwaHalting.S` to avoid clashes);
  `tmp/cmu/bin/chk FILE` retries `lake env lean` on transient host "Too many open files".
- Gotcha: `![a, b] 0` inside `decide (0 < _)` leaves a `Nat.decLt 0 (![a,b] 0)` instance after
  simp that no lemma matches; state Fin-2 lemmas over `v : Fin 2 → ℕ` / `gc x y` and pass
  `decide_eq_true (by omega)` explicitly.
- `hoff_of`/`goff_of` take target state & counters as implicit plain variables so `rfl` can
  assign them (projections of metavariables can't be assigned).
