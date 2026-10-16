# HANDOFF: rcwa-sameorbit (KICKOFF-2026-10-16-rcwa-sameorbit.md)

Branch `wip/rcwa-sameorbit-2`.  Target: every `sorry` in `CollatzMoonshot/RcwaSameOrbit.lean`.

## Done (all ratified statements unchanged; `/tmp`-style statement check against f0fe61a passes)

- Chore: `Int.le_induction` → `Int.leInduction` in `RcwaMachine.lean` (both uses, 421 and 453).
- Layer 1: `isRcwa23_eval`, `tableFrom_spec` (helpers `tableSlope`, `tableRow`, `tableRow_spec`;
  note `tableFrom` elaborates `List.range M` through a `List ℕ → List ℤ` bind, handled in
  `tableFrom_getElem` via `List.map_eq_flatMap`).
- Layer 2: `step_eq_of_fires`, `step_injective`, `isSourceB_iff` (helper `exists_rule_of_step`).
- Layer 3: `enc_spec`, `F_eq_some_iff`, `F_eq_move`, `move_slope`, `F_injective` (helpers
  `phase_lt_ord`, `decode_move`, `decode_inj`, `zpow_toNat`).
- Layer 4: `hwPoint_hwPos`, `hwPos_hwPoint`, `sigma_bijective`, `sameCycle_hwNext_iff`,
  `sameCycle_enc_iff`, `sameCycle_all_iff`.  Section `Assembly` opens `RcwaMachine` and builds
  `Good.eng`, `Good.theta`, `Good.tau` (`tauPt` + `Equiv.ofBijective`), `Good.completeFun_eq`
  (σ is the completion conjugated by `ℤ ≃ ℤ ⊕ Empty`), `sameCycle_transfer`, `Good.fwd_eng`,
  `Good.diverges_iff`, `Good.noBiInfinite`, `Good.endToStart`.
  Axioms: `propext, Classical.choice, Quot.sound`.

- `isHighway_highwayAt`: `line_of_modEq` (line periodic mod `hwModulus`) from
  `isSource_congr` (being a source depends only on the state and `min cᵢ 2`) and
  `min_padicValInt_eq` (valuations capped at `K` agree mod `p^K`).  `highwayAt` also elaborates
  `List.range` through a bind; `highwayAt_eq` normalizes it.
- `isRcwa23At_sigma`: three cases on the class of `r` mod `3^N L` (`decode_class`: engine
  membership, phase and zero pattern constant): a rule piece (`scale_spec`, `b = 0`), a highway
  step (`hwNext_affine`), and highway ∘ `τ` (`τ n · 3^{E⁻} = n · 3^{E⁺}`; the `3^N` factor makes
  the class of `τ n` mod `L` constant).
- Layer 5: `good_of_valid`, `tableOf_spec`, `not_computable_sameCycle` (uses `computable_reduce`).

- `computable_reduce`: `PrimInt` proves `ℤ` arithmetic primitive recursive by transport through
  `(a, b) ↦ a − b` (`int_natSub`, using `encode (n : ℤ) = 2n`, `encode -[n+1] = 2n + 1`):
  `int_add/neg/sub/mul/le/ediv/emod/dvd/natAbs`, plus `nat_pow`, `nat_gcd` (via
  `Nat.findGreatest`), `padicValInt` (via `Nat.findGreatest`), parameterized `list_find?`,
  `list_all`, `list_filter`.  `phase` is moved off `ZMod (5^j)` (`phase_eq`), `InEngine` gets a
  decidable form (`inEngine_iff_dec`), `tableFrom` loses `ℚ` (`tableFrom_eq`, `numZ`, `denN` from
  `Rat.num_mkRat`/`den_mkRat`), `sigma` is an `Option.getD` (`sigma_eq_getD`).  Then every
  definition is proved `Primrec` in composition form (`pr_*`), and `reduce` is `Primrec`, hence
  `Computable`.

## Status: DONE

`CollatzMoonshot/RcwaSameOrbit.lean` is sorry-free; all ratified statements unchanged (checked
textually against `f0fe61a`).  `#print axioms` of `not_computable_sameCycle`, `sameCycle_enc_iff`,
`sameCycle_all_iff`, `isRcwa23At_sigma`, `computable_reduce`, `tableOf_spec`:
`propext, Classical.choice, Quot.sound`.  `RcwaEngineGen.lean` untouched; `RcwaMachine.lean` only
the `Int.leInduction` chore.  No `native_decide`, no axioms.  The literature input remains the
hypothesis `HaltingUndecidable`.
