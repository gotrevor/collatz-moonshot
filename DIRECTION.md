# DIRECTION — collatz-moonshot

## CURRENT DIRECTIVE  (altitude laps are the ONLY writers; this OUTRANKS any HANDOFF)

> [!NOTE]
> Set by the **altitude lap of 2026-09-02**.  The previous directive — discharge
> `Assumed.rozier_terracol_3_2` — is **COMPLETE** (`55a119b`; `finite_acyclicParadoxical_imp_noDivergent`
> and `rozier_terracol_3_2` both print the bare trust base).  Do not restart it.

- 🎯 **THE OBJECTIVE: the odd-block ladder, rung 3.**  Prove
  `FrontA.threeBlock_gap_of_long` (`FrontA/ThreeBlock.lean`), hence
  `threeBlock_not_acyclicParadoxical_of_long`, hence the rung-3 classification:
  **every acyclic paradoxical segment whose word has three odd blocks has length 8.**
  Rungs 1 (Rozier–Terracol App. A) and 2 (`le_two_blocks_not_acyclicParadoxical`) are closed;
  rung 3 is the first rung whose answer is a *classification* rather than an exclusion, and it
  is the natural Front-A analogue of Front B's `m`-cycle ladder.

- **WHY THIS AND NOT THE OTHERS.**  Ranked by probability of new mathematics:
  · **(a) rung 3 — CHOSEN.**  It is the only candidate that is simultaneously (i) on the
    Front-A path (`FiniteAcyclicParadoxical` is the open hypothesis of the trust-base-clean
    closer), (ii) genuinely open, and (iii) already reduced this lap to a *finite explicit
    census* — 27 tuples at four lengths — rather than an open Diophantine wall.
  · **(b) Rhin-lite tower extraction into a shared Lake package** — deferred.  It is packaging,
    not mathematics, in this repo; `~/src/normal-numbers` is owned by another session and is
    read-only here, so the payoff cannot even be landed from this side.  Revisit as an
    *interface proposal* once rung 3 is settled.
    ⚠️ **Its advertised cross-repo payoff is REFUTED — do not re-attempt it.**  The kickoff
    prompt says to specialize `rhinLiteLIMeasure_explicit` at a zero log-3 coefficient to
    discharge normal-numbers' Tier-1 node `LnTwoExpSep`.  That node is not open.  Host
    computation, 2026-09-02: `log(3/2) + log(4/3) = log 2`, so `q = r = 2ⁿ`, `p = −p'` turns
    the form `|p + q·log(3/2) + r·log(4/3)|` into `|2ⁿ·log 2 − p'|` at height
    `H = max(|p'|, 2ⁿ) = 2ⁿ`, giving `‖2ⁿ log 2‖ ≥ rhinLiteSepC · 2^(−436n)` — i.e.
    `LnTwoExpSep` at **β ≈ 437**, against a **β = 9** already proved over there.  ~48×
    weaker, and it cannot touch their β<9 wall either (that wall is missing PNT-strength
    `lcm(1..ℓ) ≤ e^{(1+ε)ℓ}` in mathlib v4.33.1; the Rhin-lite Chebyshev envelope is the same
    `4^ℓ` bound they already use).
    **Evidence tiers, stated because this directive gets summarized:** β = 9 exists at *grep
    tier* (`theorem lnTwoExpSep_sharp : ∃ N₀, LnTwoExpSep 9 N₀`,
    `~/src/normal-numbers/src/NormalNumbers/LnTwoExpSepSharp.lean`, file clean of `sorry`,
    independently grepped by a second session).  Its axiom-cleanliness is *prose tier only* —
    their `PENDING_WORK`/`HANDOFF` claim the trust triple, but no one here ran
    `#print axioms`; do not upgrade that wording without running it.  The β ≈ 437 figure is
    *hand-computation tier*: arithmetic on the **statement** as read from source, not a Lean
    proof.  Enough to keep a lap off a dead payoff; **not** citable.  If anything load-bearing
    needs it, formalize the specialization first — that is a cheap, well-defined green node.
    What survives of (b) is only the **architecture**: normal-numbers already built its half of
    the door (`lnTwoDyadicSep_iff_int`, `src/NormalNumbers/DiophantineWall.lean`) which strips
    all orbit/digit language, and its docstring names `sep_two_three` as knocking at the same
    wall in the polynomial-coefficient regime.  This repo has no counterpart.  A shared
    separation-interface node family — with the one-log and two-log tiers as *definitional*
    instances — would make the gap between β = 9 and exponent 436 a stateable question instead
    of an artifact of two codebases.  That is the queued follow-on once rung 3 lands or is
    refuted; it is **not** tonight's objective.
  · **(c) Kolmogorov–Sinai entropy for the one-sided 2-adic shift** — deferred.  It is a
    multi-lap mathlib-infrastructure build (measure-theoretic entropy where mathlib carries
    only topological entropy) on the *Rigidity* front, with no rung-level payoff and no
    contact with the paradoxical crux.
  · **`native_decide` → `decide +kernel`** — still hygiene, still not a lap goal.

- **MANDATED NEXT MOVE — chip the census gap, hardest case first.**  The lap of 2026-09-02
  landed, sorry-free, the whole rung-3 engine: `threeBlock_master`, `threeBlock_slack`,
  `threeBlock_criterion` (acyclicity ⟺ `D·w₁ ≤ 3^f·T − 2^(c+d+e+f)`), `threeBlock_cascade`
  (the integer cascade `3^b w₁ + 2^c = 2^(c+d) w₂ + 1`, `3^d w₂ + 2^e = 2^(e+f) w₃ + 1`,
  `3^f w₃ = 2^g y + 1`), `threeBlock_of_gap`, `threeBlock_segment_identities`, and the
  **block-merge reduction** (`threeBlock_le_of_AB_C` / `_A_BC` / `threeBlock_merge_reduction`)
  that reuses rung 2 as a black box on both two-block sub-segments.  What is open is exactly
  the census.  Attack it in this order:
  1. **Eliminate `w₂` and prove the two-regime split.**  `3^(b+d) w₁ = 2^(c+d+e+f) w₃ − T`.
     Regime I (`3^d ≤ 2^(e+f)`): the ceiling on `w₂` is a bounded correction and the
     division-free real relaxation (R3) carries the argument.  Regime II (`3^d > 2^(e+f)`):
     `w₂ = 1` is *forced*, and the substitution `w₂ = 1` gives a strictly stronger bound.
     Prove each regime separately; the census says both terminate.
  2. **Both regimes funnel into `D · 2^f ≲ 3^k · 2^b`** — a linear form in **two** logs, so
     `sep_two_three` (already axiom-free in this repo) is the available Baker input if the
     elementary route stalls.  Record which regime actually needs it: that answer *is* the
     effectivity-asymmetry finding against Front B.
  3. Only then the finite tail: the 10 ceiling-passing tuples at `m ∈ {5,16,27}` are killed by
     the true realizing residue (host-verified 2026-09-02, margins of 10²–10³), and the 17 at
     `m = 8` are the exceptional length.

- 🚫 **FORBIDDEN drift.**
  · **No three-block *exclusion*.**  `acyclicParadoxical_seven_eight` refutes it in-kernel.
    Rung 3 is a **classification** (`length = 8`), which is compatible; do not restate it as an
    exclusion, and do not weaken `le_two_blocks_not_acyclicParadoxical`.
  · Never restore the "unbounded paradoxical starts" form of `rozier_terracol_3_2`
    (kernel-refuted by `noNontrivialCycle_of_unboundedParadoxicalStarts`).
  · No Rhin-lite κ-sharpening / crossover re-tuning (refuted low-leverage, 2026-09-01); no
    reopening of the elementary `b + d ≤ 5` route (refuted 2026-08-25).
  · **Do not park `threeBlock_gap_of_long` in `wip/`.**  It is the active crux; `src/`
    sorry-freedom is the completion end-state, not a per-lap gate.
  · Front B `Compression` / more block-word vocabulary — still blocked and mis-scoped.

### Directive history
- 2026-09-02 (altitude lap): **Retargeted to the odd-block ladder, rung 3.**  Previous objective
  (discharge `rozier_terracol_3_2`) certified complete.  Ranked the operator candidates and chose
  (a); deferred (b) as cross-repo packaging and (c) as off-path mathlib infrastructure.  Landed the
  whole rung-3 engine sorry-free (`FrontA/ThreeBlock.lean`) and **isolated the crux to a finite
  census**: the exact criterion plus the *two-level integer ceiling* leaves 27 tuples at
  `m ∈ {5,8,16,27}` (exhaustive `m ≤ 130`), while the real relaxation alone is provably infinite
  (18 → 258 → 2489 → 18324 tuples at `m = 8, 16, 27, 46`).  Finding: rung 3's finiteness is carried
  by interior integrality, not by a linear form in logarithms — an effectivity asymmetry against
  both rung 2 and Front B's `m`-cycle ladder.
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
