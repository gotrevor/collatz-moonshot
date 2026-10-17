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
- §6 classification + mirror: all closed (`hyp_gPerm`, `hyp_gmPerm`, counts, lower bounds,
  both `InfinitelyManyInfiniteOrbits`).  Mirror partial runs `j < m` need `x ≤ 3/5`
  (`gRoot_le_of_pos`, from `x² ≥ 2(2x − 1)` when `m ≥ 1`); helper
  `le_wy_iterate_of_even_run_mirror`.  `densityG_eq` closed.
  Gotchas: `Φ` is not a valid identifier character (`hzΦ` breaks the parser: use `hzF`);
  structure-instance `refine { … }` across lines failed to parse, anonymous `⟨…⟩` works.
  Box builds intermittently hit "Too many open files" (environmental); retry loop `/tmp/lb.sh`.
- Open (4): `coneEntry_infinite`, `tendsto_coneEntryCount` (Cone), `tendsto_minCount_gPerm`,
  `tendsto_minCount_gmPerm` (Line §7).  Next: `coneEntry_infinite` (unconditional; Dirichlet
  syndeticity of `T` vs. log-sparse forward orbits from a finite entry set).
- `coneEntry_infinite` closed (no logs needed): syndetic `T` (`coneSet_syndetic`: Dirichlet
  `Real.exists_int_int_abs_mul_sub_le` + `fract_hit`), entry map (`exists_entry`, strong
  induction), and on `T` every later orbit point is `≥ 3/2 ×` an earlier one, so each entry's
  forward orbit has at most one point in `[Y, 3Y/2)`; `N + 1` window points inject into `E`.
- Open (3): `tendsto_coneEntryCount` (Weyl 1-dim), `tendsto_minCount_gPerm/gmPerm` (Weyl multi).
- `tendsto_coneEntryCount` closed: `phaseCount`, `card_coneSet_Icc` (= phaseCount (X/2)),
  `card_image_coneSet_Icc` (= phaseCount ⌊(X+1)/α⌋₊, irrationality excludes `kα = X + 1`),
  generic `tendsto_floor_linear_div`, `tendsto_comp_div`.  `WythoffCone.lean` sorry-free.
- Open (2): `tendsto_minCount_gPerm`, `tendsto_minCount_gmPerm` (§7, multi-dim Weyl).
- §7 engine landed (`WythoffLine.Engine`): `Nf x ρ ψ` (N₀ = ⌊2ψ₀⌋, N_{l+1} = ⌊2ψ_{l+1} +
  x(ρ + N_l − 2ψ_l)⌋), `volume_cyl` (= 2⁻¹^|I|, via half-translation `volume_cyl_flip`; no
  Fubini), `volume_frontier_cyl` (finite union of convex level sets, `Convex.addHaar_frontier`).
  ρ = 1 main (odd runs, step v ↦ ⌊xv + x⌋), ρ = 0 mirror (even runs, v ↦ ⌊xv⌋).
  **Plan for the two densities:** (a) run lemma: if `W(n₀) = ⌊2kA⌋` and the first `l` iterates
  have parity ρ, `W^{l+1}(n₀) = N_l(Ψ k) + 2⌊kAxˡ⌋`, `Ψ k = ({k A xⁱ})_{i<m}`; (b) returnTime
  = j+1 ⟺ Ψ k ∈ `cyl (range (min (j+1) m)) (update (const ρ) j (ρ+1))`; (c) |R − 2kAxʲ| < 4
  from the sandwiches; (d) squeeze with `tendsto_comp_div`/`tendsto_floor_linear_div`, sum
  over j; (e) independence of `Fin.cons 1 (A xⁱ)` from `hind` (multiply by xᵐ, `A xᵐ = r`);
  (f) algebra `1/2 − Σ_{j<m} 1/(2αβʲ) − 1/(αβᵐ) = (α−2)/(2αβᵐ)`.  m = 0: α = 2r rational, run
  lemma vacuous (hypotheses gated on `1 ≤ m`).

## DONE (2026-10-17)

All four files sorry-free; `lake build CollatzMoonshot.WythoffLine CollatzMoonshot.WythoffCone`
green; `#print axioms` of `tendsto_minCount_gPerm/gmPerm`, `gPerm/gmPerm/wkPerm_
infinitelyManyInfiniteOrbits`, `tendsto_coneEntryCount` = `[propext, Classical.choice,
Quot.sound]`.  Every ratified statement/def checked unchanged against `2769ba3` (script compared
110 declaration headers).  Weyl hypotheses stay hypotheses; `hind` stays a hypothesis.
§7 route as planned above: `section Density` in `WythoffLine.lean` (`run_Nf`, `wordSet`,
`returnTime_eq_iff`, `tendsto_returnCount_div`, `linearIndependent_theta`, `tendsto_wordCount`,
`density_sum_eq`), instantiated with ρ = 1 (`gPerm`, `n₀ = 2k`) and ρ = 0 (`gmPerm`,
`n₀ = 2k − 1`).
