# collatz-moonshot 🌙

[![CI](https://github.com/gotrevor/collatz-moonshot/actions/workflows/ci.yml/badge.svg)](https://github.com/gotrevor/collatz-moonshot/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

> [!IMPORTANT]
> **This repository does not prove the Collatz conjecture, the absence of divergent
> orbits, or the absence of nontrivial cycles.** It is an exploratory Lean 4 research
> project. At this checkpoint the project builds, but two theorems contain a disclosed
> `sorry` (`sep_two_three` and `rhinLiteLIMeasure`, the latter a concrete route to the
> former), several conditional results depend on explicitly named axioms, and computational
> searches provide evidence rather than proofs.

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
| `sep_two_three` | a disclosed `sorry`; an effective separation statement for powers of 2 and 3 (the sink node of the two-block exclusion) |
| `rhinLiteLIMeasure` | a disclosed `sorry`; the coarse Rhin linear-independence measure of `{1, log(3/2), log(4/3)}`, from which `log23_effective_measure` (the `log₂3` irrationality measure feeding `sep_two_three`) is proved |
| named declarations in `CollatzMoonshot/Assumed/` | explicit external assumptions, some published results and some open conjectures |
| `native_decide` certificates | kernel-checked finite computations, retained in theorem axiom ledgers as `native_decide` artifacts |

In particular, the single-log Legendre development is ancillary: it formalizes useful
approximant machinery for `log 2`, but it does **not** prove the simultaneous
`log 2`/`log 3` estimate required by `sep_two_three`.

The current independent two-log experiment is more direct: `FrontA/RhinLite.lean` proves exact
arithmetic balances and a coarse central-coefficient band `17^n ≤ B_n ≤ 18^n` for a rationalized
Rhin kernel. `FrontA/RhinLiteCritical.lean` exhausts the relevant roots of its degree-8 critical
polynomial, and `FrontA/RhinLiteInterval.lean` proves the exact local `(9/40)^1000` remainder bound.
The compact-maximum, integral, and log-form wiring are complete; `FrontA/RhinLiteApprox.lean`
now reduces `sep_two_three` to the single Rhin linear-independence measure `rhinLiteLIMeasure`
(via the trust-base-clean change of basis `linForm_eq_log23`, the elimination identity
`elim_identity`, and the proved-from-crux `log23_effective_measure`). See
[FRONT-A-RHIN-LITE.md](FRONT-A-RHIN-LITE.md); this progress does not discharge `sep_two_three` yet.

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
