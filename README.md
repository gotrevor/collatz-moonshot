# collatz-moonshot 🌙

[![CI](https://github.com/gotrevor/collatz-moonshot/actions/workflows/ci.yml/badge.svg)](https://github.com/gotrevor/collatz-moonshot/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

> [!IMPORTANT]
> **This repository does not prove the Collatz conjecture, the absence of divergent
> orbits, or the absence of nontrivial cycles.** It is an exploratory Lean 4 research
> project. At this checkpoint the project carries **one disclosed `sorry`**,
> `threeBlock_gap_of_long` (`FrontA/ThreeBlock.lean`) — the active research crux, the census gap
> of rung 3 of the odd-block ladder, opened on 2026-09-02. Every Front-A closer is unaffected:
> `finite_acyclicParadoxical_imp_noDivergent` and `Assumed.rozier_terracol_3_2` print the bare
> trust base (the classical Diophantine node `two_pow_approx_three_pow_from_above` was proved on
> 2026-09-01). The sink
> separation `sep_two_three` (powers of 2 and 3) is **proved from first principles** via the
> Rhin-lite construction (`FrontA/RhinLiteSep.lean`), so the formerly cited Rhin 1987 axiom is
> retired from the build; several conditional results still depend on explicitly named axioms,
> and computational searches provide evidence rather than proofs.

The project splits Collatz into its two logically independent failure modes—an
unbounded orbit and a nontrivial cycle—and develops candidate machinery for each.
Its purpose is to make proposed reductions precise, expose hidden assumptions, record
counterexamples to tempting false statements, and identify the genuinely difficult
mathematical inputs.

## Proof status

The most important distinction in this repository is between Lean-checked wiring and
the open hypotheses fed into that wiring:

| item | status |
| --- | --- |
| `conjecture_iff_split` | proved in Lean: Collatz is equivalent to `NoDivergentOrbit ∧ NoNontrivialCycle` |
| Front A: no divergent orbit | open; the repository proves several conditional implications |
| Front B: no nontrivial cycle | open; the current compression target does not close the front |
| `sep_two_three` | **proved, no literature axiom** (`FrontA/RhinLiteSep.lean`): the effective separation statement for powers of 2 and 3 (the sink node of the two-block exclusion), from the explicit Rhin-lite measure `rhinLiteLIMeasure_explicit` (κ=436, `c = 1/(2·(396/5)^6000·6^436)`), the crossover `crossover_exp_436_141000` (`k ≥ 141000`), five kernel-checked convergent brackets of `log₂3` on `450 ≤ k < 141000`, and the `native_decide` table on `6 ≤ k < 450`; ledger = trust base + `native_decide` certificates |
| `rhinLiteLIMeasure` | **proved** (`FrontA/RhinLiteApprox.lean`): the coarse Rhin linear-independence measure of `{1, log(3/2), log(4/3)}` from the Rhin-lite kernel — existential constants; its explicit-constant form is `rhinLiteLIMeasure_explicit` |
| Rhin 1987 (`rhin_1987_log_two_three_measure`) | **retired** 2026-09-01: no longer in the build; the axiom and the old `κ=14` route are parked in `wip/Rhin1987.lean`, `wip/RhinAxiomRoute.lean` |
| `rozier_terracol_3_2` (Rozier--Terracol 2026, Thm 3.2) | **corrected, then DISCHARGED, 2026-09-01.** The axiom previously claimed *unboundedly large* paradoxical starts `2^k n`; that reading is strictly stronger than the published theorem and provably implies `NoNontrivialCycle` (an open problem) — see the in-repo kernel refutation `noNontrivialCycle_of_unboundedParadoxicalStarts`. Restated as the paper's cardinality claim, it is now a **proved theorem** of `Assumed/Paradoxical.lean`, **trust-base clean** (`#print axioms` = `propext, Classical.choice, Quot.sound`) |
| `two_pow_approx_three_pow_from_above` (`FrontA/PowApprox.lean`) | **proved** 2026-09-01, trust base only: for all `M N` there are `A > M` and `s` with `3^A < 2^s` and `(2^s − 3^A)·N ≤ 3^A`, i.e. powers of two approximate powers of three from above to arbitrary relative precision, infinitely often. Multiplicative pigeonhole: the `N+1` ratios `2^s/3^A ∈ (1,2]` at `A = i(M+1)` fall into `N` boxes `((1+1/N)^j, (1+1/N)^(j+1)]`, a collision gives `2^b/3^a` within `1+1/N` of `1` on both sides with `a > M`, and a flip (least `u` with `(3^a/2^b)^(u+1) ≥ 2`) fixes the side. No logarithms, no irrationality of `log₂3`, no `native_decide`. With it `finite_acyclicParadoxical_imp_noDivergent` is trust-base clean |
| `le_two_blocks_not_acyclicParadoxical` | **proved, no literature axiom**, and **sharp**: `acyclicParadoxical_seven_eight` exhibits an acyclic paradoxical segment (`n=7`, `m=8`) whose word has three odd blocks, so no three-block strengthening exists |
| named declarations in `CollatzMoonshot/Assumed/` | explicit external assumptions, some published results and some open conjectures |
| `native_decide` certificates | kernel-checked finite computations, retained in theorem axiom ledgers as `native_decide` artifacts |

In particular, the single-log Legendre development is ancillary: it formalizes useful
approximant machinery for `log 2`, but it does **not** prove the simultaneous
`log 2`/`log 3` estimate required by `sep_two_three`.

The current independent two-log experiment is more direct: `FrontA/RhinLite.lean` proves exact
arithmetic balances and a coarse central-coefficient band `17^n ≤ B_n ≤ 18^n` for a rationalized
Rhin kernel. `FrontA/RhinLiteCritical.lean` exhausts the relevant roots of its degree-8 critical
polynomial, and `FrontA/RhinLiteInterval.lean` proves the exact local `(9/40)^1000` remainder bound.
The compact-maximum, integral, and log-form wiring are complete, the determinant crux is closed,
and `rhinLiteLIMeasure` (`FrontA/RhinLiteApprox.lean`) is proved. `FrontA/RhinLiteSep.lean` makes
its constants explicit (`κ = 436`; the `lcmUpto` majorant `lcmUpto(2000t) ≤ (22/5)^(2000t)` holds
for every `t ≥ 1`, so no asymptotic threshold survives) and re-wires `sep_two_three` onto it:
the explicit measure gives `m·log2 − k·log3 ≥ c/k^436` on the near-critical window, the crossover
`k^436 ≤ c·2^(k/3)` holds for `k ≥ 141000`, and the finite range is closed by five consecutive
convergent brackets of `log₂3` (largest certificate `2^478245 < 3^301739`, `decide +kernel`) plus
the existing `k < 450` table. The cited Rhin 1987 axiom is therefore retired from the build. See
[FRONT-A-RHIN-LITE.md](FRONT-A-RHIN-LITE.md).

Run `#print axioms <theorem>` to inspect a theorem's dependency ledger. A successful
`lake build` means Lean accepted the files; it does not erase a `sorry`, validate the
truth or fidelity of a declared axiom, or establish that an experimental reduction is
useful for Collatz. See [CollatzMoonshot/Assumed.lean](CollatzMoonshot/Assumed.lean) for
the axiom policy and [STATUS.md](STATUS.md) for the detailed research ledger.

## Repository map

- [APPROACHES.md](APPROACHES.md) is the global strategy map.
- [FRONT-A-ROUTES.md](FRONT-A-ROUTES.md) tracks the divergence front.
- [FRONT-A-RHIN-LITE.md](FRONT-A-RHIN-LITE.md) tracks the independent coarse two-log proof.
- [FRONT-B-ROUTES.md](FRONT-B-ROUTES.md) tracks the cycle front.
- `CollatzMoonshot/Basic.lean`, `Conjecture.lean`, and `Descent.lean` define the map,
  conjecture, two-front split, and descent equivalence.
- `CollatzMoonshot/FrontA/` contains backward-tree, rigidity, parity, paradoxical-window,
  and power-separation work.
- `CollatzMoonshot/FrontB/` contains parity-word, cycle, and circuit-compression work.
- `CollatzMoonshot/Assumed/` contains provenance-documented assumptions; assumptions are
  kept separate from the project's own targets.
- `experiments/` contains exploratory computations. Their output is not a proof unless a
  corresponding Lean theorem checks it.
- `papers/` contains original reading notes; source PDFs are intentionally not tracked.

`STATUS.md`, `DIRECTION.md`, `PENDING_WORK.md`, dated `HANDOFF-*.md` files, and online
findings are a chronological lab notebook. They preserve failed routes and changing
judgments, so older entries may be stale or contradicted by later ones. The table above
is the concise public status statement; Lean source and `#print axioms` are authoritative.

`ON-LINE-FINDINGS-*.md` record answers to source requests filed while development ran
without network access. The request queue itself was transient and has been retired, so
lab notes that call a request “unanswered” describe the state at that time and are
superseded by the findings files.

## Build

The repository is pinned to Lean `v4.33.1` and the matching mathlib tag.

```bash
git clone https://github.com/gotrevor/collatz-moonshot.git
cd collatz-moonshot
lake exe cache get
lake build
```

CI performs the same cached mathlib setup and build on pushes and pull requests.
The public proof-debt and representative axiom-ledger checks can also be run directly:

```bash
bash scripts/check-proof-debt.sh
lake env lean scripts/AxiomAudit.lean
```

## Provenance and authorship

Development is directed by Trevor Morris and has been heavily AI-assisted, principally
by Claude (nicknamed “Ren”) and Codex. Lean checks proof terms relative to their listed
dependencies; it does not check research novelty, literature summaries, or whether a
formal statement faithfully represents a cited paper. Those require human review.

Some lab notes mention `collatz-cryptid`, a separate private predecessor repository. It
is not a build dependency. Third-party code adaptation is recorded in
[THIRD_PARTY.md](THIRD_PARTY.md).

## License and citation

Released under the [Apache License 2.0](LICENSE). Citation metadata is provided in
[CITATION.cff](CITATION.cff).
