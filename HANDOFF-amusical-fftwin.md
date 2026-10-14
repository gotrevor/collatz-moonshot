# HANDOFF: amusical F₂[t] twin complete (2026-10-14)

Branch `wip/amusical-fftwin`; proof commit `9c23705` (on top of `4349cd4`).  Run stopped by
`box done --green` after the scoped target was met.

## Concrete advance

Scoped target complete: `CollatzMoonshot/AmusicalFunctionField.lean` is sorry-free and every
ratified statement/definition (`twinQ`, `twinU`, `twinCycle`) is unchanged; only the two
"Target" docstrings were relabelled "Proved".  No new axiom, no `native_decide`, no large
`decide`.  Lines ≤ 100 characters.

- `twinU_bijective` := `FFTwin.fU_bijective` (`AmusicalFunctionField/Basic.lean`).  `fQ`/`fU` are
  verbatim copies of `twinQ`/`twinU`, so the main file closes by definitional unfolding.  Branch
  lemmas `fU_E/A/B/C`, four-way decomposition `fU_cases` (via `X_pow_dvd_iff`), injectivity by
  uniqueness of `Q k + s`, `deg s < 2` (`div_modByMonic_unique`), surjectivity by
  `modByMonic_add_div` plus `eq_X_add_C_of_natDegree_le_one`.
- `twinCycle_minimalPeriod` := `FFTwin.fU_minimalPeriod` (`AmusicalFunctionField/Cycle.lean`).
  Closed-form orbit, cleaner than the kickoff's itinerary-primitivity route:
  * `E` phase `fU_iterate_E`: `U^j (t^(j+s) c) = Q^j t^s c`.
  * `B` phase: `P k = e_B (u^{m−3} Q^m + t^{3(m−k)} G k)`, `G (k+1) = Q G k + t^{3k}`.  Key
    lemma `fU_of_step`: any `P` with `t³ P' = Q P + e_B` is in the `B` branch and `U P = P'`
    (so branch membership never needs a separate low-coefficient computation).  `P_step` is
    that identity, from Frobenius `u^m Q^m = t^{3m} + 1` (`frob_uQ`).
  * Closing `P_last`: `u³ G k = Q^k + t^{3k}`, `(t u)^m = 1 + Q^m` (`frob_tu`), cancel `u³`.
  * Exactness: period divides `2^(n+1)`; `U^m x₀ = P 0` has constant term 1, `x₀` has 0.
- Tactic recipe for char-2 identities in `(ZMod 2)[X]`:
  `linear_combination (norm := (ring_nf; reduce_mod_char)) c * h`.  Generalize symbolic powers
  (`X^(3k)`, `Q^m`, …) to atoms first.

## Verification

```text
taskset -c 0-3 lake build            # Build completed successfully (8899 jobs)
#print axioms twinU_bijective, twinCycle_minimalPeriod, twin_infinitelyManyCycles
  # [propext, Classical.choice, Quot.sound]
```

Box note: "Too many open files" recurred on wide builds and even `lake env lean`; `taskset -c
0-3` (or a retry) clears it.  Spurious, environmental.

## Next

Target met; nothing in flight.  Host: merge `wip/amusical-fftwin` to `main`.  The open mathematical question recorded in the module docstring ("one infinite
orbit exists" for the twin) is not a target of this run.
