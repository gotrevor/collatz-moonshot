# STATUS — collatz-moonshot 📊
**A machine-checked scaffold for the Collatz conjecture: an axiom-clean two-front
decomposition, with each front's deep inputs as honestly-cited axioms being narrowed
lap by lap.** · **Build**: 🟢 green (8747 jobs) · **Updated**: review lap · 2026-08-24 · Front A M2′ redirect

## Where it stands
The headline wiring is done and axiom-clean: `conjecture_iff_split` and
`conjecture_of_fronts` (`Conjecture.lean`, `Descent.lean`) reduce Collatz to two
front-hypotheses — `NoDivergentOrbit` (Front A, divergence) and `NoNontrivialCycle`
(Front B, cycles) — using only `propext/choice/Quot.sound`. Both fronts are open. **This
review re-scoped the reachable frontier.** Front B's closer needs `Compression` (an *upper*
bound on cycle circuit-count) — now diagnosed as Front B *restated* (no elementary/known
upper bound; the literature bounds circuits only below) and **source-blocked** (SdW 2005 not
on box); its Lean apparatus is feature-complete and **on hold**. Front A's live route is
**M2′** — `ParityRigidityW1' → NoDivergentOrbit` — whose only gap is a Krylov–Bogolyubov
measure module (mathlib has the surrounding Prokhorov + Portmanteau + drift plumbing). The
local-certificate lane is harmonic-capped below α=1 (proved, complete). `src/` is sorry-free.

## What's happened (newest first)
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
- **Front A M2′ measure module** (binding crux): build the Krylov–Bogolyubov step for
  `ParityRigidityW1' → NoDivergentOrbit` — empirical Cesàro measures' cluster points are
  `T2`-invariant (telescoping `2/N` bound + pushforward weak-* continuity), + the uniform
  `limsup` bound from W1′ over the weak-*-compact invariant-measure set. Endpoints done.
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

Cited axioms in `Assumed/` + `FrontB/Threads.lean` (the discharge frontier, not yet on a
headline's uncond path): `eliahou_min_cycle_length` 🟡, `hercher_odd_members_bound` 🟡,
`hercher_min_circuit_count` 🟡, `baker_bounded_difference` 🟠 (Baker/Tijdeman),
`furstenberg_topological_rigidity` 🟠 (proved 1967, unformalized), `tao_2019_almost_bounded`
🟡 (proved upstream), `collatz_verified_*` 🟢, `abc` 🔴 (open conjecture — used ONLY in
results that are themselves stated conditional on abc). No 🔴 appears on any unconditional
headline.

## Pointers
- Binding directive: `DIRECTION.md` → CURRENT DIRECTIVE
- Routes: `FRONT-A-ROUTES.md` (§A1 = M2′ route), `FRONT-B-ROUTES.md`,
  `FRONT-A-HARMONIC-DUAL.md` (done)
- Newest baton: `HANDOFF-2026-08-24-2330.md` · scratchpad: `PENDING_WORK.md`
