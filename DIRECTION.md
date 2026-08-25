# DIRECTION — collatz-moonshot

## CURRENT DIRECTIVE  (altitude laps are the ONLY writers; this OUTRANKS any HANDOFF)

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

- **MANDATED next move:** Continue the paradoxical project's NEW mathematics — the two-block
  exclusion `le_two_blocks_not_acyclicParadoxical` (strictly generalizes RT Appendix A). It is
  machine-checked **modulo the single inequality `b + d ≤ 5`** (the sole `src/` `sorry`, in
  `near_critical_containment`); everything else — the elementary squeeze, `window_unique_m`, the
  power bracket, and the finite discharge once `b+d ≤ 5` — is sorry-free.
  **`b + d ≤ 5` is now DEFINITIVELY Baker-grade** (effective irrationality of `log₂3`): the review
  lap 2026-08-25-1500 REFUTED the last elementary hope by proving the real relaxation of
  `¬A∧¬B∧subcrit∧U₁ ⇒ b+d≤5` is FEASIBLE at unbounded `g` (fully-checked witness at `g=41`,
  `experiments/two_block_relaxation.py`), so NO `nlinarith`/polynomial certificate can exist.
  **Attack ONLY the GO route:** build an explicit effective irrationality / linear-forms-in-logs
  lower bound for `log₂3` in Lean — mathlib lacks it (only `LiouvilleWith`).
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
  parametric `sep_of_uniform_measure` at the true `C`. Core is 🟡 project-scale, **not** 🟠
  generational, but leg 3 (the two-*kernel* simultaneous form) is a genuine multi-lap expedition
  (integer transfinite diameter of `[2,4]`, effective two-sided coefficient asymptotics `n(ε)`).

  **MANDATED next chip = the single-log effective measure (leg 2 → real result).** `Legendre.lean`
  now has, all trust-base-clean, the whole single-kernel toolkit: linear form
  `∫₀¹ P_n/(1−a·y) = A + B·log(1−a)` (`legendre_mobius_linear_form`), geometric remainder bound,
  and non-vanishing (`legendre_mobius_ne_zero`). The concrete next move — findings-blessed as the
  warm-up that exercises **all three legs** — is **denominator/integrality tracking**: for `a : ℤ`,
  `a ≤ −1` (so `1−a ∈ {2,3,…}`, giving `log 2` at `a=−1`, `log 3` at `a=−2`), prove
  `∃ P Q : ℤ, lcm(1..n)·a^(n+1)·Λ_n = P + Q·log(1−a)` via the per-moment integrality
  `∃ s:ℤ, lcm(1..k)·a^(k+1)·∫y^k/(1−a·y) = s − lcm(1..k)·log(1−a)` (induction on
  `mobius_moment_rec`, using `k+1 ∣ lcm(1..k+1)` and `lcm(1..k) ∣ lcm(1..k+1)`). Combined with
  `legendre_mobius_ne_zero` + the remainder bound + `Gelfond.lcmUpto_le`, this yields a **genuine
  effective irrationality measure of a single log in Lean** (mathlib has none) — real novel content,
  and the exact denominator machinery leg 3 reuses two-kernel-wise. Discharging `sep_two_three` →
  GO. A cited Rhin/Gelfond axiom or a larger census stays BASELINE and MUST NOT clear the
  src-sorry gate.

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
  (SdW not on box) → put on hold, forbid more block vocabulary. Redirected the binding
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
  expedition (transfinite diameter, effective `n(ε)` asymptotics). Set MANDATED next chip = single-log
  denominator/integrality tracking (findings-blessed warm-up, exercises all 3 legs, yields the first
  effective irrationality measure of a log in Lean). Build 🟢 8754 jobs; crux `sep_two_three` unchanged
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
