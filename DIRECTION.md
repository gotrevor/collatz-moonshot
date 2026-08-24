# DIRECTION — collatz-moonshot

## CURRENT DIRECTIVE  (altitude laps are the ONLY writers; this OUTRANKS any HANDOFF)

- **THE objective:** Advance the two genuinely-open headline cruxes of the repo,
  hardest-first. The headline `conjecture_of_fronts (hA : NoDivergentOrbit)
  (hB : NoNontrivialCycle) : Conjecture` is axiom-clean; all the real difficulty is
  the two front hypotheses. Both are open. The route-decisive blockers are:
  - **Front B:** `Compression` (`FrontB/Threads.lean`) — *upper* bound on the circuit
    count of a primitive nontrivial integer cycle. With `hercher_min_circuit_count`
    (≥92, no-transcendence) this closes Front B via `frontB_of_compression_le_91`.
    **This upper bound is absent from the literature** (Hercher/SdW bound circuits
    *below*, the "never-finishes" direction). Pure combinatorics-on-words + integrality.
  - **Front A:** complete a `DivergentDescentCertificate` → `NoDivergentOrbit`. The
    local-certificate constructive lane is **harmonic-capped below α=1** (proved last
    session), so redirect to itinerary-rigidity (Tao2019 cited/ok + Furstenberg cited).

- **MANDATED next move:** Attack `Compression` with the smallest source- or
  compiler-grounded probe that tests it — decompose it into named Lean sub-goals
  grounded in the S-unit/integrality structure, formalize a prerequisite, or read
  Simons–de Weger (request PDF via `ON-LINE-REQUEST.md`; not on-box) for a concrete
  decomposition. A full proof is multi-year; each lap NARROWS, recording the advance
  (or refuted sub-approach) in `PENDING_WORK.md`. If Front B stalls, the Front A
  itinerary-rigidity redirect is the alternate crux.

- **FORBIDDEN drift (do NOT spend a lap on):**
  - Grinding the `OneCircuit` a≥2 case as an *elementary* `omega` argument — it is
    **Steiner's theorem = Baker/transcendence**, and it is off the critical path
    (`hercher_min_circuit_count` already covers every rung ≤91). It is resolved
    honestly by the isolated `SteinerOneCircuit` hypothesis; leave it.
  - Porting another harmonic/subharmonic exponent — that project is COMPLETE.
  - Route-1 gcd-harvest (`Threads.lean` Thread 7) — KILLED; rotations give one condition.
  - Off-path leaf sorries, docs-only laps, or freezing a finite table as a headline.

- **WHY:** Per-lap progress tempts toward tractable leaves (harmonic no-go, one-circuit
  base) while the two real cruxes go untouched. Both cruxes are open research; the
  honest deliverable is genuine narrowing of the hardest reachable one, not manufactured
  green on side-work.

### Directive history
- 2026-08-24 (review lap): harmonic-dual project certified COMPLETE. Diagnosed
  `OneCircuit` a≥2 as Steiner/Baker (not `omega`) and off critical path; resolved it via
  explicit `SteinerOneCircuit` hypothesis (no new axiom, sorry removed). Set the binding
  objective to the two open fronts, Front B `Compression` first. Created DIRECTION.md +
  STATUS.md.

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
