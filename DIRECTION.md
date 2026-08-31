# DIRECTION — collatz-moonshot

## CURRENT DIRECTIVE  (altitude laps are the ONLY writers; this OUTRANKS any HANDOFF)

> [!NOTE]
> Public checkpoint, 2026-08-25: no treadmill is active. This section supersedes the
> dated directive history below, which is retained as a research log.

- 🎯 **The objective is novel PROOFS — new mathematics.  Novel *formalization* is not the point
  here, at all** (operator, 2026-08-29: "The entire point is novel *proofs*.  This is different
  from other lean repos, where formalization *is* the point.").  Same doctrine as normal-numbers.
  Weigh every candidate move by its probability of producing new mathematics; "first in any
  prover" carries no weight in prioritization.

- **THE OBJECTIVE, restated (2026-08-29): this repo's product is a machine-checked conjecture
  GRAPH, not a proof queue.**  A unit of progress = one green **node** (a named Prop - working
  conjecture, axiom candidate, interface - kernel-elaborated, with provenance, odds, and a
  refutation probe under `experiments/`), one green **edge** (sorry-free, axiom-audited wiring),
  or one **probe-refuted node** (a kill is progress).  The FrontB thread board and `Assumed/`
  tiers are the prior art; this generalizes them to the whole repo.  Sink: `Conjecture`
  (via the two fronts).  Every lap answers: *what is the weakest open node on each path to the
  sink - add a weaker node, add an edge, or kill one.*  Grinding known mathematics is only ever
  *discharging a named node* (lane 2, KB two-lanes doctrine: phase 1 tolerates
  warnings/`native_decide`/boosts; distribution prep is separate).  The Rhin-lite campaign
  below is exactly that: lane-2 discharge of the single node `sep_two_three`.  A lap that
  cannot advance a proof can ALWAYS advance the graph.

- **Independent Rhin-lite route now active (2026-08-25).**  `FrontA/RhinKernel.lean` proves the
  exact arithmetic/content balances of Rhin's published kernel.  `FrontA/RhinLite.lean` uses the
  nearby denominator-1000 kernel `(705,551,449,109,39,54)/1000` and machine-checks the complete
  central-coefficient band `17^n ≤ B_n ≤ 18^n` along its block subsequence.  No saddle-point or
  coefficient asymptotic remains. `FrontA/RhinLiteCritical.lean` proves that eight disjoint
  sign-changing brackets exhaust the real roots of the degree-8 critical polynomial (so no Sturm
  theory was needed), and `FrontA/RhinLiteInterval.lean` proves the full rational target
  `|H(x)|/x^1000 ≤ (9/40)^1000` on all seven possible critical brackets.
  `FrontA/RhinLiteMaximum.lean` now closes the compact-maximum/derivative bridge globally on
  `[2,4]`, sorry-free. `FrontA/RhinLiteEven.lean` now lifts that base estimate to the even block
  subsequence `N = 2000t`: exact degree `2N`, central-coefficient band `17^N ≤ B_N ≤ 18^N` (via
  the `comp (-X)` identification with `rhinLitePositive (2t)`), and the pointwise normalized
  integrand identity/nonnegativity/`(9/40)^N` bound — all sorry-free. **Next live theorem:** the
  two interval-integral consequences, then the two LCM-cleared integral log forms. Read
  `FRONT-A-RHIN-LITE.md` and `FRONT-A-RHIN-LITE-NEXT.md`.

- **THE objective:** Advance one of the two genuinely open headline fronts.  The reachable
  bridge on Front A has changed: **M2′ is COMPLETE**.  The sorry-free theorem
  `parityRigidityW1'_imp_noDivergent : ParityRigidityW1' → NoDivergentOrbit` now includes
  the whole empirical-Cesàro → Krylov–Bogolyubov invariance/support → uniform parity
  `limsup` → high-tail drift contradiction, and its axiom footprint is exactly
  `[propext, Classical.choice, Quot.sound]`.  Do not rebuild that measure plumbing.

- **The parity-reconstruction pull is COMPLETE and classified BASELINE / RE-SCOPE.** It
  landed a sorry-free cylinder envelope, forward residue determinacy, and the genuine
  eventually-periodic `¬Diverges` baseline. The exact reconstruction API is complete in the
  experiment. The same-suffix spread proves only that a suffix does not determine or
  uniformly approximate the normalized endpoint; it does **not** prove a universal
  finite-state no-go. Do not add routine reconstruction plumbing or repeat that experiment.

- **Actual open obligation:** Continue the paradoxical project's two-block
  exclusion `le_two_blocks_not_acyclicParadoxical` (strictly generalizes RT Appendix A). It is
  machine-checked **modulo the single inequality `b + d ≤ 5`** (the sole `src/` `sorry`, in
  `near_critical_containment`); everything else — the elementary squeeze, `window_unique_m`, the
  power bracket, and the finite discharge once `b+d ≤ 5` — is sorry-free.
  **`b + d ≤ 5` is now DEFINITIVELY Baker-grade** (effective irrationality of `log₂3`): the review
  lap 2026-08-25-1500 REFUTED the last elementary hope by proving the real relaxation of
  `¬A∧¬B∧subcrit∧U₁ ⇒ b+d≤5` is FEASIBLE at unbounded `g` (fully-checked witness at `g=41`,
  `experiments/two_block_relaxation.py`), so NO `nlinarith`/polynomial certificate can exist.
  A proof needs an effective irrationality / linear-forms-in-logs lower bound for `log₂3`.
  **Target sharpened (review lap 2026-08-25-2100).** `sep_two_three` is now reduced *sorry-free*
  (`sep_of_uniform_measure`, using `poly_le_two_pow`) to ONE uniform pure-ℕ bound
  `∀ near-critical k ≥ K:  3^k ≤ (2^m − 3^k)·k^C`. That is exactly a **classical effective
  irrationality measure of `log₂3`** (linear forms in *two* logs) — a *polynomial* measure,
  exponentially stronger than the `2^(−k/3)` this crux needs. **Honest constants (findings
  2026-08-25):** the proven object is **Rhin 1987**'s lin-indep measure of `{1,log2,log3}`;
  the *fully explicit, threshold-free* exponent is `E = 13.3` ⇒ **`C = 15`, `k ≥ 400`** (exact
  crossover `k^45 ≤ 2^k` at `k = 387`); the asymptotic `7.616+ε` carries an unpublished `H₀(ε)`.
  Bennett–Bugeaud is OFF-path (quadratic irrationals). `C = 6/k ≥ 130`
  (`sep_two_three_of_gelfond_measure`) is **illustrative only**; the honest interface is the
  parametric `sep_of_uniform_measure` at the true `C`. Formalizing that literature from first
  principles is a substantial, source-sensitive project; leg 3 (the two-*kernel* simultaneous form)
  is a genuine multi-lap expedition
  (integer transfinite diameter of `[2,4]`, effective two-sided coefficient asymptotics `n(ε)`).

  **Do not continue the single-log detour merely to prove `Irrational (Real.log 2)`.**
  `Legendre.lean` now has a useful, trust-base-clean single-kernel package: an integer
  linear form, non-vanishing, and a geometric remainder for `log 2`. This is standard
  auxiliary mathematics and does not give the simultaneous `log 2`/`log 3` estimate.
  If work resumes, either (a) state the exact published Rhin-style input as a narrow,
  provenance-audited named axiom, consistent with `Assumed.lean`, or (b) undertake the
  two-kernel formalization as its own explicit objective. Do not imply that the single-log
  package itself advances `sep_two_three`.

- **Front B remains on hold.**  `Compression` asks for an upper bound on the circuit count
  of a primitive nontrivial cycle and is Front B restated once combined with Hercher's lower
  bound.  Its block/S-unit/rotation apparatus is feature-complete; resume only if the missing
  Simons–de Weger source or a genuinely new upper-bound idea changes the mathematics.

- **FORBIDDEN drift (do NOT spend a lap on):**
  - **Front B `Compression` / more block-word vocabulary** — blocked + mis-scoped (above);
    the apparatus is feature-complete. Wait for the SdW source or a new idea.
  - Grinding the `OneCircuit` a≥2 case as an *elementary* `omega` argument — it is
    **Steiner's theorem = Baker/transcendence**, off the critical path
    (`hercher_min_circuit_count` covers every rung ≤91). Resolved by the isolated
    `SteinerOneCircuit` hypothesis; leave it.
  - Porting another harmonic/subharmonic exponent — that project is COMPLETE.
  - Rebuilding M2′, proving only its converse calibration, or adding more empirical-measure
    plumbing — M2′ is COMPLETE; the converse is useful calibration but not the live crux.
  - A prefix-local forbidden-word search: every finite parity word is realized by a residue
    class. A finite-state argument is admissible only when its global transition inequality
    or carry/height content is load-bearing; suffix collisions alone are not a no-go theorem.
  - Route-1 gcd-harvest (`Threads.lean` Thread 7) — KILLED; rotations give one condition.
  - **The "elementary A/B route" for `b+d ≤ 5`** (`¬A∧¬B∧subcrit∧U₁ ⇒ b+d≤5` via nlinarith/omega
    over exponent atoms) — REFUTED (real relaxation feasible at unbounded `g`; no certificate
    exists). Also the `le_of_gap_A/B` decomposition of that plan, and any restart of "maybe some
    clever elementary inequality bounds `b+d`/`d`" — all void; the finiteness is Baker-forced.
  - Off-path leaf sorries, docs-only laps, or freezing a finite table as a headline.

- **WHY:** Paradoxical segments make the additive remainder—the information discarded by
  density heuristics—exactly load-bearing. They are finite, enumerable, and admit a clean
  word criterion, while the literature proves that a divergent/infinite-stopping orbit would
  force infinitely many of them. This does not make the route easy: global finiteness is
  stronger than Collatz. It does give a current, falsifiable place to discover structural
  lemmas rather than extending formal vocabulary.

### Directive history
- 2026-08-24 (review lap): harmonic-dual project certified COMPLETE. Diagnosed
  `OneCircuit` a≥2 as Steiner/Baker (not `omega`) and off critical path; resolved it via
  explicit `SteinerOneCircuit` hypothesis (no new axiom, sorry removed). Set the binding
  objective to the two open fronts, Front B `Compression` first. Created DIRECTION.md +
  STATUS.md.
- 2026-08-24 (review lap, later): **RE-SCOPED.** Established Front B `Compression` is
  Front B restated (no elementary/known upper bound on circuit count) AND source-blocked
  (the needed SdW source was unavailable) → put on hold, forbid more block vocabulary. Redirected the binding
  objective to **Front A M2′** (`ParityRigidityW1' → NoDivergentOrbit`): confirmed mathlib
  has Prokhorov + Portmanteau-on-clopen; isolated the sole gap as a Krylov–Bogolyubov
  module; landed the two pure M2′ endpoints (`exists_freqThreshold_gt`,
  `not_diverges_of_eventually_lt`) and the precise 3-piece decomposition in PENDING_WORK.
- 2026-08-24 (M2′ completion + audit): `parityRigidityW1'_imp_noDivergent` proved with the
  full KB/support/frequency/drift chain and independently rebuilt/audited at the trust base.
  Redirected the live Front-A pull to the parity-reconstruction/carry barrier; see
  `FRONT-A-PARITY-RECONSTRUCTION.md`.
- 2026-08-24 (parity reconstruction completion + post-run audit): landed the exact
  experiment and sorry-free Lean baseline. Corrected the run's overclaim: endpoint spread
  within a suffix class is not a universal finite-state obstruction. Classified the pull
  BASELINE / RE-SCOPE and redirected to `FRONT-A-PARADOXICAL.md`.
- 2026-08-25 (review lap): paradoxical project executed → PROMISING EVIDENCE confirmed. Made
  real crux progress: DECOMPOSED `le_two_blocks_not_acyclicParadoxical` and PROVED Case A
  (both blocks subcritical) sorry-free via two head-block applications + word-split. Isolated
  the residual to one arithmetic core (GOAL2', joint 2-adic/3-adic residue force) shared by
  Cases B/C; wrote the reconstruction route + failed simple bounds into PENDING_WORK. Kept
  the objective on this new-mathematics crux (proving it = GO).
- 2026-08-25 (review lap, 1500): **REFUTED the "elementary A/B route" for the crux `b+d ≤ 5`.**
  Proved (exact-rational witness at `g=41`, `experiments/two_block_relaxation.py`) that the real
  relaxation of `¬A∧¬B∧subcrit∧U₁ ⇒ b+d≤5` is feasible at unbounded `g`, so NO nlinarith/
  polynomial certificate exists (verified in-Lean: couplings compile, nlinarith fails). The
  integer-truth is Baker-forced. Redirected the MANDATED next move to the sole GO path: build
  effective irrationality of `log₂3` (linear forms in logs) in Lean; forbade all further
  elementary-inequality attempts on `b+d`. Axiom audit re-run: two headline consumption theorems
  clean (trust base + faithful `rozier_terracol_3_2`); two-block exclusion carries the single
  disclosed `sorryAx` (the `b+d≤5` crux).
- 2026-08-25 (review lap, 2100): **Route-decisive source read — crux core reclassified 🟡, target
  sharpened.** Identified `sep_two_three`'s residual as the classical **Gelfond 1935 / Bennett–Bugeaud**
  effective `|2ⁿ−3ᵐ|` bound (polynomial measure ≫ the exponential needed) — 🟡 project-scale, not the
  pessimistic 🟠. Landed sorry-free (trust base) `poly_le_two_pow` + `sep_of_uniform_measure`,
  machine-checking that ONE uniform measure `3^k ≤ (2^m−3^k)·k^C` (large k) + finite check ⇒ the full
  crux. Kept GO on the effective bound; next narrowing = discharge finite check at concrete `C`, then
  build the Padé/Gelfond core. Build 🟢 8752 jobs.
- 2026-08-25 (review lap, this one): **Direction KEPT (GO on effective measure), constants corrected,
  next chip pinned.** Findings landed: the object is **Rhin 1987** (`{1,log2,log3}` measure), honest
  explicit exponent `E=13.3 ⇒ C=15, k≥400`; `C=6` is unprovable from literature (illustrative only);
  Bennett–Bugeaud is off-path. Confirmed leg 1 (`Gelfond.lcmUpto_le`) + full single-kernel leg 2
  (`Legendre.lean`) are trust-base clean; leg 3 (two-*kernel* Rhin determinant) is a real multi-lap
  expedition (transfinite diameter, effective `n(ε)` asymptotics). The run then set a single-log
  denominator/integrality warm-up as its next chip; the public-readiness review later classified
  that work as ancillary. Build 🟢 8754 jobs; crux `sep_two_three` unchanged
  disclosed sorry.

---

## Standing charter (destination)

Prove the Collatz headline `Conjecture ↔ NoDivergentOrbit ∧ NoNontrivialCycle`
(`Conjecture.lean`, `Descent.lean`) by discharging the cited axioms behind each front
into machine-checked proofs, keeping `lake build` green and every headline
`#print axioms`-honest. "Done" = every headline's base is the trust base +
`native_decide` artifacts + genuinely-discharged inputs, with `🔴` open-conjecture
axioms appearing ONLY inside results the mathematics itself states conditionally.

Guardrails (repo-wide): a claim is real only when the kernel accepts it with a clean
`#print axioms`; disclosed `sorry`/cited axioms are honest, faked proofs are not; never
claim a Collatz result stronger than what is actually proved.
