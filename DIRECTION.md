# DIRECTION — collatz-moonshot

## CURRENT DIRECTIVE  (altitude laps are the ONLY writers; this OUTRANKS any HANDOFF)

- **THE objective:** Advance one of the two genuinely open headline fronts.  The reachable
  bridge on Front A has changed: **M2′ is COMPLETE**.  The sorry-free theorem
  `parityRigidityW1'_imp_noDivergent : ParityRigidityW1' → NoDivergentOrbit` now includes
  the whole empirical-Cesàro → Krylov–Bogolyubov invariance/support → uniform parity
  `limsup` → high-tail drift contradiction, and its axiom footprint is exactly
  `[propext, Classical.choice, Quot.sound]`.  Do not rebuild that measure plumbing.

- **The remaining Front-A crux is arithmetic.**  `ParityRigidityW1'` itself must
  distinguish parity itineraries of ordinary positive integers from the unrestricted
  2-adic full shift.  The next funded pull is the exact inverse-parity reconstruction/carry
  machine in `FRONT-A-PARITY-RECONSTRUCTION.md`: a shortcut parity prefix determines a
  unique residue modulo `2^m`; extending the prefix emits one binary digit of the starting
  integer and updates an exact unbounded carry/endpoint.  A positive integer is precisely
  the asymptotic case where those output bits are eventually zero.  A divergent orbit would
  have to combine that condition with critical odd density and aperiodicity.

- **MANDATED next move:** Execute the experiment-first project in
  `FRONT-A-PARITY-RECONSTRUCTION.md`.  Build and exhaustively validate the exact online
  reconstruction recurrence; search for a depth-independent carry invariant or a precise
  obstruction to bounded-memory potentials; formalize the small residue/carry kernel and
  the eventual-periodicity no-divergence baseline in Lean.  This is a research probe, not a
  directive to claim W1′.  Stop and re-scope if the result is only the known prefix bijection
  plus routine plumbing—do not extend vocabulary indefinitely.

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
  - A bounded-suffix parity automaton or finite forbidden-word search: every finite parity
    word is realized by a residue class.  Carry/height information must be load-bearing.
  - Route-1 gcd-harvest (`Threads.lean` Thread 7) — KILLED; rotations give one condition.
  - Off-path leaf sorries, docs-only laps, or freezing a finite table as a headline.

- **WHY:** M2′ compressed Front A to a single honest statement and thereby exposed exactly
  what remains: positive-integer conditioning.  Prefix reconstruction turns that vague
  phrase into an exact input/output machine and supplies a falsifiable place to seek new
  mathematics.  The finite-prefix surjectivity is also a guardrail: successful rigidity
  must be asymptotic or use unbounded carry/archimedean state.

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
