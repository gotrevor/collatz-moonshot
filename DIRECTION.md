# DIRECTION — collatz-moonshot

## CURRENT DIRECTIVE  (altitude laps are the ONLY writers; this OUTRANKS any HANDOFF)

> [!NOTE]
> Set by the review lap of **2026-09-01 (later)**.  It replaces the whole previous directive,
> whose mandated moves (`sep_two_three`, `rhinLiteLIMeasure`, the `b + d ≤ 5` crux) are all
> **DONE**.  Detail lives in `PENDING_WORK.md`; the standing charter below is unchanged.

- 🎯 **THE OBJECTIVE: discharge `Assumed.rozier_terracol_3_2`** — the *only* cited axiom left
  under a Front-A headline — into a machine-checked proof, so that
  `finite_acyclicParadoxical_imp_noDivergent` becomes trust-base clean.

- **MANDATED NEXT MOVE — split the axiom by orbit boundedness and prove the bounded half first,
  then attack the unbounded half as a Diophantine node.**  Fix `n ≥ 2` with
  `InfiniteStoppingTime n`; the goal is `{p | Paradoxical (2^p.1 * n) p.2}.Infinite`.
  · **(A) bounded shortcut orbit** — the orbit is eventually periodic, entering a cycle of
    period `L` at time `t`.  The cycle block is subcritical (`subcritical_of_tstep_cycle`,
    proved 2026-09-01), so the coefficient `3^a / 2^m` of `m = t + jL` tends to `0`; for large
    `j` it drops below `1` while the endpoint stays `≥ n`.  Infinitely many pairs `(0, m)`.
    **Fully elementary — prove this case outright.**  (`infinite_paradoxical_of_tstep_cycle`
    already does the special case `t = 0`.)
  · **(B) unbounded shortcut orbit** — reduce to the named node
    `∃ᶠ j, ∃ k, 3^(a_j) / 2^j < 2^k ≤ (tstep^[j] n) / n`  (an integer power of `2` separating
    the multiplicative coefficient from the normalized endpoint; this is exactly the
    equivalence `3^a < 2^(k+j) ∧ 2^k n ≤ tstep^[j] n`).  That is RT's "infinitely many left
    approximations `3^a/2^b < 1` of `1`" step, and it is the natural consumer of the repo's
    own `log₂3` apparatus (`PowSeparation`, `sep_of_bracket_nat`, the convergent brackets).
    State the node in `src/` as a disclosed `sorry` and chip it.

- 🚫 **FORBIDDEN drift.**
  · **Never restore the "unbounded paradoxical starts" form of the axiom.**  It is refuted
    in-kernel (`noNontrivialCycle_of_unboundedParadoxicalStarts`): it proves `NoNontrivialCycle`
    outright.  Any restatement must be checked against that theorem.
  · No three-block strengthening of `le_two_blocks_not_acyclicParadoxical` — refuted by the
    kernel witness `acyclicParadoxical_seven_eight` (`n=7, m=8`, three odd blocks).  The
    two-block exclusion is exactly sharp; the discovery ladder is finished.
  · No further Rhin-lite κ-sharpening / crossover re-tuning (refuted low-leverage, 2026-09-01),
    and no reopening of the elementary `b + d ≤ 5` route (refuted 2026-08-25).
  · Front B `Compression` / more block-word vocabulary — still blocked and mis-scoped.
  · Converting the Rhin-lite `native_decide` certificates to `decide +kernel` is hygiene, not a
    lap goal.

- **WHY.**  As of 2026-09-01 the Front-A two-block exclusion is fully machine-checked (trust
  base + `native_decide` artifacts, no literature axiom), so `rozier_terracol_3_2` is the single
  remaining non-trust-base dependency of a Front-A headline.  Its hard half is precisely the
  left-approximation-of-1 object that ten laps of Rhin-lite work built the machinery for, and
  its easy half is a clean elementary win available now.  Nothing else in the repo has that
  combination of on-path-ness and reachability.

### Directive history
- 2026-09-01 (review lap): **Caught and repaired a fidelity BUG at a headline's base.** The
  `rozier_terracol_3_2` axiom read "unboundedly large paradoxical starts `2^k n`"; machine-checked
  that this implies `NoNontrivialCycle` (open), hence is strictly stronger than Rozier--Terracol
  Thm 3.2. Restated the axiom in its published cardinality form, kept the refutation
  (`noNontrivialCycle_of_unboundedParadoxicalStarts`) and a non-vacuity anchor
  (`infinite_paradoxical_of_tstep_cycle`) in `src/`, and re-derived
  `diverges_imp_infinite_acyclicParadoxical` through an injection. Also pinned
  `acyclicParadoxical_seven_eight` (three odd blocks), proving the two-block exclusion sharp and
  closing the discovery ladder. **Redirected the objective** from the (completed) `sep_two_three`
  campaign to discharging `rozier_terracol_3_2`, decomposed bounded / unbounded orbit.
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
