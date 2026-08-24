# STATUS — collatz-moonshot 📊
**A machine-checked scaffold for the Collatz conjecture: an axiom-clean two-front
decomposition, with each front's deep inputs as honestly-cited axioms being narrowed
lap by lap.** · **Build**: 🟢 green (8751 jobs) · **Updated**: 2026-08-25 · two-block exclusion decomposed, Case A proved

## Where it stands
The headline wiring is done and axiom-clean: `conjecture_iff_split` and
`conjecture_of_fronts` (`Conjecture.lean`, `Descent.lean`) reduce Collatz to two
front-hypotheses — `NoDivergentOrbit` (Front A, divergence) and `NoNontrivialCycle`
(Front B, cycles) — using only `propext/choice/Quot.sound`. Both fronts are open. **This
review re-scoped the reachable frontier.** Front B's closer needs `Compression` (an *upper*
bound on cycle circuit-count) — now diagnosed as Front B *restated* (no elementary/known
upper bound; the literature bounds circuits only below) and **source-blocked** (SdW 2005 not
on box); its Lean apparatus is feature-complete and **on hold**. Front A milestone **M2′ is
complete**: `ParityRigidityW1' → NoDivergentOrbit` is sorry-free and trust-base clean, including
all Krylov–Bogolyubov/Portmanteau/frequency/drift plumbing. The remaining Front-A crux is
`ParityRigidityW1'` itself—the arithmetic restriction distinguishing positive-integer parity
itineraries from the unrestricted 2-adic shift. The inverse-parity reconstruction pull is
complete and classified BASELINE / RE-SCOPE. The
local-certificate lane is harmonic-capped below α=1 (proved, complete).

**Paradoxical-window project (`FRONT-A-PARADOXICAL.md`) — delivered, classified PROMISING
EVIDENCE.** Parts A/B/C complete: exact source lock (identity, criterion (P), slack (S), the
`7→8` example); **Rozier–Terracol Appendix A formalized sorry-free** (`headBlock_not_
acyclicParadoxical`); the exact few-block `numer` closed forms; and the full Front-A
consumption `finite_acyclicParadoxical_imp_noDivergent : FiniteAcyclicParadoxical →
NoDivergentOrbit`, machine-checked with ledger `[propext, Classical.choice, Quot.sound,
rozier_terracol_3_2]` (the whole divergence→infinite-acyclic bridge discharged sorry-free).
New discovery: **every acyclic paradoxical word has ≥ 3 odd blocks** — exhaustively verified
two ways (word-based to length 38; independent orbit-based to start 100000), strictly
generalizing Appendix A. The interior two-block exclusion
(`le_two_blocks_not_acyclicParadoxical`) is now **decomposed with Case A (both blocks
subcritical) proved sorry-free**; the residual (Cases B/C, exactly one block supercritical)
reduces to one joint 2-adic/3-adic arithmetic core (`GOAL2'`). This is the active-crux
decomposition, not off-path — it carries two disclosed `src/` sorries by design.

## What's happened (newest first)
- **2026-08-25 (crux narrowed hard — elementary regime of the residue core PROVED):** Reduced
  the whole two-block exclusion to one self-contained ℕ lemma `two_block_residue_core`
  (submitted to Aristotle, job `4006e40e`), then PROVED its **elementary regime `core_of_gap`
  sorry-free**: a genuinely new contrapositive argument (exact identity `2^m·y + 2^(b+c+d) =
  3^(b+d)(n+1) + 3^d·2^b(2^c−1)`, no integrality) that a census shows covers ~99.7% of
  subcritical `(b,c,d,e)` (3791/3803 in range). The sole remaining `src/` sorry is the thin
  **residual** where the gap fails and a 3-adic least-residue bound on `w₂` is genuinely
  needed (the required bound grows with `b`). Build 🟢 8751 jobs.
- **2026-08-25 (review lap — two-block crux decomposed, Case A proved):** Made real crux
  progress on the sole `src/` sorry `le_two_blocks_not_acyclicParadoxical`. Split the
  `[T]^b[F]^c[T]^d[F]^e` itinerary at step `b+c` (`traceWord_add` + `List.append_inj`) into two
  head-block segments, then case-split on criticality. **Case A (both blocks subcritical) is now
  PROVED sorry-free** (`headBlock_endpoint_le` twice ⇒ `y ≤ X ≤ n`), and whole-word
  subcriticality is shown to forbid both-supercritical. The two residual cases B/C are reduced
  to ONE arithmetic core (`GOAL2'`, the joint 2-adic/3-adic residue force via relation (★)
  `3^b w₁ = 2^(c+d) w₂ − 2^c + 1`) with the reconstruction route + refuted simple bounds written
  into PENDING_WORK. Build 🟢 8751 jobs.
- **2026-08-24 (paradoxical-window project delivered → PROMISING EVIDENCE):** Executed
  `FRONT-A-PARADOXICAL.md` end to end. Landed `experiments/paradoxical.py` (exact source lock +
  two independent enumerators) and `CollatzMoonshot/FrontA/Paradoxical.lean` +
  `CollatzMoonshot/Assumed/Paradoxical.lean`. Formalized RT Appendix A sorry-free; proved the
  exact criterion (P)/slack (S) and few-block `numer` closed forms; discharged the entire
  Front-A consumption `finite_acyclicParadoxical_imp_noDivergent` down to the single cited RT
  Theorem 3.2 axiom (no `sorryAx`). New exhaustively-verified restriction: **≥ 3 odd blocks**
  for every acyclic paradoxical word (two independent implementations). Its full proof is a
  deep open sub-problem (2/3-adic residue interplay); proved the 2-adic foundation
  `headBlock_dvd_succ`. One disclosed active-crux `src/` sorry remains
  (`le_two_blocks_not_acyclicParadoxical`). Build 🟢 8751 jobs.
- **2026-08-24 (parity reconstruction complete + audited):** Landed the exact reconstruction
  experiment and the sorry-free cylinder-envelope/residue/eventual-periodicity Lean kernel.
  Added `normalized_endpoint_ne_start_one`, a permanent kernel-checked counterexample to a
  false normalized-endpoint claim. Corrected the broader overclaim too: same-suffix endpoint
  spread refutes suffix-only endpoint prediction, not every finite-state Lyapunov proof.
  Classified the result BASELINE / RE-SCOPE and opened `FRONT-A-PARADOXICAL.md`.
- **2026-08-24 (M2′ complete):** Proved
  `parityRigidityW1'_imp_noDivergent : ParityRigidityW1' → NoDivergentOrbit`, including
  arbitrary empirical cluster invariance/support, exact odd-frequency transport, the uniform
  sub-sharp `limsup`, and high-tail drift consumption. Full build green (8748 jobs); independent
  targeted rebuild and axiom audit report exactly `[propext, Classical.choice, Quot.sound]`.
  Re-pointed the live research pull to parity reconstruction/carries.
- **2026-08-24 (review lap, later):** **RE-SCOPED direction.** Established Front B
  `Compression` is Front B restated + source-blocked → on hold, no more block vocabulary.
  Redirected the binding crux to **Front A M2′** (`ParityRigidityW1' → NoDivergentOrbit`):
  confirmed mathlib has Prokhorov (`CompactSpace (ProbabilityMeasure ℤ₂)`) +
  Portmanteau-on-clopen; isolated the sole gap as a Krylov–Bogolyubov invariant-measure
  module; **landed the two pure M2′ endpoints** `exists_freqThreshold_gt` +
  `not_diverges_of_eventually_lt` (`Rigidity/Drift.lean`, trust-base clean) and the precise
  3-piece decomposition (`PENDING_WORK.md`, `DIRECTION.md`).
- **2026-08-24 (review lap):** Certified the harmonic-dual project COMPLETE. Diagnosed
  the `OneCircuit` a≥2 case as **Steiner's theorem (Baker/transcendence), not an `omega`
  leaf**, and **off the critical path** (Hercher covers all rungs ≤91). Resolved it via
  an explicit `SteinerOneCircuit` hypothesis — sorry removed, no new axiom, imported from
  root (`oneCircuitCanonical_trivial` is now `[propext, choice, Quot.sound]`). Created
  DIRECTION.md (binding directive → Front B `Compression`) + this STATUS.md.
- **2026-08-24:** Front B ladder-base probe: closed forms for the canonical one-circuit
  word `trueᵃfalseᵇ` (`numer = 3ᵃ−2ᵃ`, `den = 2^(a+b)−3ᵃ`), the `den ∣ numer ↔ den ∣ 2ᵇ−1`
  reduction, and the a=1 slice in full.
- **2026-08-24:** **Harmonic-dual obstruction PROVED** sorry-free & depth-uniform:
  `no_positive_harmonic_local_certificate` — the constant-lift-1 local-certificate
  architecture on floors `{1,7/4,3,6,12}` admits no positive certificate at any depth
  `k≥9` (memory-9 `native_decide` supersolution, contraction `0.99224<1`, Farkas dual).
  A no-go for one certificate scheme, NOT a Collatz-divergence claim.
- **2026-08-24:** Harmonic experiment made exact/reproducible
  (`experiments/barrier_harmonic_dual.py`): refutation surface for the α=1 gap; only
  `mod 3^9` memory suffices, no closed-form/rank-1 weight (the gap is real but structureless).
- **2026-08-23:** Exponent-4/5 backward-tree pipeline complete (2/3→3/4→4/5 rungs green);
  harmonic no-go then showed this local-certificate ladder cannot reach α=1.
- **2026-08-23:** Front B dictionary `noNontrivialCycle_iff_frontB` proved; `FrontB`
  threads restated over `Primitive` words (word-powers made the naive statements
  degenerate = `FrontB` in disguise); Route-1 gcd-harvest (Thread 7) KILLED.
- **2026-08-22:** Hercher 2023 verified firsthand (≥92 circuits, no transcendence);
  corrected the `abc`-closes-cycles overclaim (abc bounds `D` *below* only).

## Outstanding
### Short-term (mirror PENDING_WORK top)
- **Front A two-block exclusion** (binding): prove the residue core `GOAL2'` shared by Cases
  B/C. Route: formalize the `w₁/w₂` reconstruction (relation (★)), state
  `two_block_residue_bound` (which also re-proves Case A), and attack the joint 2-adic/3-adic
  minimum via `ZMod (3^b)` / least-residue. Proving it = new infinite-family theorem → project
  GO. Refuted: `w₁≥1`-only bounds are insufficient (see PENDING_WORK).
- M2′ is complete. Do not rebuild measure plumbing or spend the next project only proving
  the converse calibration `NoDivergentOrbit → ParityRigidityW1'`.
- Front B `Compression` is **on hold** (blocked + mis-scoped) — do not extend until the
  SdW source lands or a new upper-bound idea appears.
- (Optional) Prove `SteinerOneCircuit` — Steiner 1977; needs an effective irrationality
  measure for `log₂3`. Multi-year; leave isolated.
### Long-term
- Prove `ParityRigidityW1'` itself — the arithmetic intertwining making positive-orbit
  conditioning visible to ×2×3 rigidity (FRONT-A-ROUTES §A1, "no route close"). M2′ makes
  W1′ a valid sufficient condition; this is the genuinely-open new mathematics behind it.
- Discharge / narrow the Front B cited axioms (`baker_bounded_difference`, `eliahou`,
  `hercher_*`); consider adopting the stronger Hercher–Bařina unconditional bound.
- Reopen Front B `Compression` if the SdW source or a new upper-bound idea arrives.
### To completion
- Both fronts unconditional (or each conditional exactly where the mathematics is), all
  cited axioms discharged or reduced to trust base + `native_decide` + genuine citations.

## Axiom ledger (per headline theorem)
Trust base = `propext, Classical.choice, Quot.sound` (+ `native_decide` `ax_*` artifacts),
excluded from the math-axiom count below.

| headline theorem | paper claim | `#print axioms` shows (beyond trust base) | math-axioms |
|---|---|---|---|
| `conjecture_iff_split` | uncond (finite wiring) | — | 0 ✅ |
| `conjecture_of_fronts` | uncond (finite wiring) | — | 0 ✅ |
| `noNontrivialCycle_iff_frontB` | uncond (dictionary) | — | 0 ✅ |
| `frontB_of_compression_le_91` | Front B closer | `hercher_min_circuit_count` | 1 · 🟡 proved (Hercher 2023, no transcendence; `Compression` still an *open def*, not an axiom) |
| `two_pow_68_lt_of_onCycle_nontrivial` | conditional demo | `collatz_verified_up_to_two_pow_68` | 1 · 🟢 finite computation |
| `no_positive_harmonic_local_certificate` | no-go (one scheme) | 4× `native_decide.ax` | 0 math · 🟢 finite checks |
| `parityRigidityW1'_imp_noDivergent` | Front A conditional closer | — | 0 ✅ (`ParityRigidityW1'` is an explicit hypothesis/`def`, not an axiom) |

Cited axioms in `Assumed/` + `FrontB/Threads.lean` (the discharge frontier, not yet on a
headline's uncond path): `eliahou_min_cycle_length` 🟡, `hercher_odd_members_bound` 🟡,
`hercher_min_circuit_count` 🟡, `baker_bounded_difference` 🟠 (Baker/Tijdeman),
`furstenberg_topological_rigidity` 🟠 (proved 1967, unformalized), `tao_2019_almost_bounded`
🟡 (proved upstream), `collatz_verified_*` 🟢, `abc` 🔴 (open conjecture — used ONLY in
results that are themselves stated conditional on abc). No 🔴 appears on any unconditional
headline.

## Pointers
- Binding directive: `DIRECTION.md` → CURRENT DIRECTIVE
- Routes: `FRONT-A-PARADOXICAL.md` (live), `FRONT-A-PARITY-RECONSTRUCTION.md` (done),
  `FRONT-A-ROUTES.md`,
  `FRONT-B-ROUTES.md`, `FRONT-A-HARMONIC-DUAL.md` (done)
- M2′ completion baton: `HANDOFF-2026-08-24-1730.md` · scratchpad: `PENDING_WORK.md`
