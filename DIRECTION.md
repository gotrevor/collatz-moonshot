# DIRECTION — collatz-moonshot

## CURRENT DIRECTIVE  (altitude laps are the ONLY writers; this OUTRANKS any HANDOFF)

- **THE objective:** Advance the two genuinely-open headline cruxes of the repo,
  hardest-first. The headline `conjecture_of_fronts (hA : NoDivergentOrbit)
  (hB : NoNontrivialCycle) : Conjecture` is axiom-clean; all the real difficulty is
  the two front hypotheses, both open. **This review re-scoped the reachable frontier:**
  - **Front B `Compression` is BLOCKED and was mis-scoped as tractable.** It asks for an
    *upper* bound `C` on the circuit count of a primitive nontrivial integer cycle. Three
    facts, established this lap: (a) with `hercher_min_circuit_count` (≥92) any `C ≤ 91`
    gives *no nontrivial cycle*, so `Compression` is **Front B restated**, not a sub-lemma
    — an upper bound on `m` is as hard as the cycles problem; (b) the literature bounds `m`
    only *below* (SdW 68→76, Hercher 77→91), because a small-`m` cycle over-approximates
    `log₂3`; as `m` grows the constraint relaxes, so **no upper bound exists in the record
    and none follows elementarily**; (c) it is source-blocked — Simons–de Weger 2005 is
    **not on box** and the `ON-LINE-REQUEST.md` is unanswered. Its Lean apparatus
    (block/S-unit/rotation) is feature-complete. **Building more Front B vocabulary is
    forbidden drift.** Front B is on hold pending either the SdW source or a genuinely new
    idea for an upper bound.
  - **Front A M2′ is the reachable, on-path crux to fund.** `NoDivergentOrbit` follows
    from the parity-rigidity keystone `ParityRigidityW1'` via the **owed** implication
    `ParityRigidityW1' → NoDivergentOrbit` (milestone M2′, `Rigidity/Invariant.lean`). The
    local-certificate lane is harmonic-capped below α=1 (proved, COMPLETE), so M2′ is the
    live Front-A route. mathlib supplies the plumbing: Prokhorov weak-* compactness
    (`CompactSpace (ProbabilityMeasure ℤ₂)`), Portmanteau on the clopen parity set
    (`ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto`), the drift consumption
    (`lt_of_oddSteps_freq_lt`), and now the two M2′ endpoints (`exists_freqThreshold_gt`,
    `not_diverges_of_eventually_lt`, `Rigidity/Drift.lean`, this lap). The **single genuine
    gap** is a Krylov–Bogolyubov invariant-measure module (absent from mathlib): empirical
    Cesàro cluster measures of the orbit are `T2`-invariant, and the invariant-measure set
    is weak-* compact so W1′ bounds the empirical `limsup` *uniformly* below
    `sharpThreshold`. See `PENDING_WORK.md` for the exact 3-piece decomposition.

- **MANDATED next move:** Build the Krylov–Bogolyubov measure module for M2′ (the smallest
  compiler-grounded probe first: state the empirical-measure invariance lemma, prove the
  telescoping bound `‖T∗μ_N − μ_N‖ ≤ 2/N` and pushforward weak-* continuity, then the
  cluster-measure invariance). Each lap NARROWS it; record the advance (or refuted
  sub-approach) in `PENDING_WORK.md`. Do NOT touch Front B `Compression` until the SdW
  source lands or a genuinely new upper-bound idea appears.

- **FORBIDDEN drift (do NOT spend a lap on):**
  - **Front B `Compression` / more block-word vocabulary** — blocked + mis-scoped (above);
    the apparatus is feature-complete. Wait for the SdW source or a new idea.
  - Grinding the `OneCircuit` a≥2 case as an *elementary* `omega` argument — it is
    **Steiner's theorem = Baker/transcendence**, off the critical path
    (`hercher_min_circuit_count` covers every rung ≤91). Resolved by the isolated
    `SteinerOneCircuit` hypothesis; leave it.
  - Porting another harmonic/subharmonic exponent — that project is COMPLETE.
  - Route-1 gcd-harvest (`Threads.lean` Thread 7) — KILLED; rotations give one condition.
  - Off-path leaf sorries, docs-only laps, or freezing a finite table as a headline.

- **WHY:** Recent laps built feature-complete Front B block vocabulary and Front A W1′
  *arithmetic* leaves while both true summits stayed untouched — the crux-neglect pattern.
  Front B's summit has no known/elementary handle and no on-box source, so it is not a
  compiler probe this lap. Front A's M2′ is the reachable on-path measure-theory build the
  headline genuinely reuses; its only gap (Krylov–Bogolyubov) is buildable in mathlib.

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
