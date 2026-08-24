# STATUS — collatz-moonshot 📊
**A machine-checked scaffold for the Collatz conjecture: an axiom-clean two-front
decomposition, with each front's deep inputs as honestly-cited axioms being narrowed
lap by lap.** · **Build**: 🟢 green (8747 jobs) · **Updated**: review lap · 2026-08-24 · `eb3a51a`+wip

## Where it stands
The headline wiring is done and axiom-clean: `conjecture_iff_split` and
`conjecture_of_fronts` (`Conjecture.lean`, `Descent.lean`) reduce Collatz to two
front-hypotheses — `NoDivergentOrbit` (Front A, divergence) and `NoNontrivialCycle`
(Front B, cycles) — using only `propext/choice/Quot.sound`. Both fronts are genuinely
open and rest on cited axioms. Front B's closer needs `Compression` (an *upper* bound
on cycle circuit-count, **absent from the literature**) on top of the proved
`hercher_min_circuit_count` (≥92). Front A needs a `DivergentDescentCertificate`; its
local-certificate constructive lane was proved (last session) to be **capped below the
harmonic exponent α=1**, so it redirects to Tao2019/Furstenberg itinerary-rigidity.
`src/` root chain is sorry-free.

## What's happened (newest first)
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
- Attack Front B `Compression` (upper bound on circuit count) — decompose into named
  Lean sub-goals / read Simons–de Weger for a concrete decomposition (PDF not on-box:
  request via `ON-LINE-REQUEST.md`).
- (Optional) Prove `SteinerOneCircuit` — this is Steiner 1977; needs an effective
  irrationality measure for `log₂3`. Multi-year; leave isolated for now.
### Long-term
- Front A itinerary-rigidity: build a `DivergentDescentCertificate` from Tao2019 +
  Furstenberg topological rigidity (the constructive local-certificate lane is α-capped).
- Discharge / narrow the Front B cited axioms (`baker_bounded_difference`, `eliahou`,
  `hercher_*`); consider adopting the stronger Hercher–Bařina unconditional bound.
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
- Routes: `FRONT-A-ROUTES.md`, `FRONT-B-ROUTES.md`, `FRONT-A-HARMONIC-DUAL.md` (done)
- Newest baton: `HANDOFF-2026-08-24-0610.md` · scratchpad: `PENDING_WORK.md`
