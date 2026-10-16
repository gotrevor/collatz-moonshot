# HANDOFF wythoff-solvable (live notes)

Kickoff: `KICKOFF-2026-10-16-wythoff-solvable.md`.  Branch `wip/wythoff-solvable`.

## Progress

- §1 `WythoffGeneral.lean`: all 8 sorries closed (helpers `one_lt_beta`, `floor_strictMono`,
  `ceil_strictMono`).
- §2 `MonotonePotential.lean` (Lemma P): all 18 sorries closed.  Engine: `desc_chain` (a run
  of `d` points off `S` descends by `≥ d`), `lt_pow_of_mem` (after an `S`-point everything is
  strictly larger; strong induction using (H2)'s `τ`), `add_le_pow_of_mem` (gain `≥ k` after
  `k·T` steps), `back_not_mem` (no `S`-visit at backward time `≥ x·T`), `back_ge`,
  `no_back_mem` (T-predecessor test ⇒ no earlier `S`-visit), `returnTime_eq`.  Orbit minimum
  exists by well-foundedness alone.  Gotcha: `push_cast` rewrites `(σ ^ n) z` to
  `σ^[n] z` (`Equiv.Perm.coe_pow`); omega handles `↑(d + 1)` itself.  Filter-instance
  mismatch (`x ∈ S \ Φ`, classical vs `Set.decidableSdiff`): close with `convert … using 2;
  ext; simp only [Finset.mem_filter]`.
- §3 `WythoffCone.lean`: 15 of 17 closed (A′, cone/anticone bounds, irrationality via
  `sq_eq_of_between`, trap, recurrence, entry characterisation, Theorem K modulo
  `coneEntry_infinite`).  Open: `coneEntry_infinite`, `tendsto_coneEntryCount`.
- §4 `WythoffLine.lean` root/parameters: all closed (`gRoot_spec` IVT, `gRoot_unique` via
  `no_two_roots` = `convexOn_pow` + `slope_mono_adjacent`, `irrational_gRoot` by hand rational
  root theorem with `Rat.reduced` + `IsCoprime.isUnit_of_dvd'`, `alphaG_*`, `alphaG_one`).
- §5 identities: all 4 closed.  `run_sandwich` / `run_sandwich_mirror` carry the two-sided
  bound in the multiplied-out form `(1 − x)(v − A xʲ n) ≤ x − x^{j+1}` (no geometric sums);
  `wy_even_bounds`, `wy_odd_bounds` are the one-step real bounds for any `α`.  Gotcha:
  `rw [betaG]` also unfolds inside `wy (betaG m r)`; rewrite `betaG m r / 2 = x` instead.
