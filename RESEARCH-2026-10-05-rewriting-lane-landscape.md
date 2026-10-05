# The rewriting / termination-certificate lane: who is already there, and the target it hands us

5 October 2026.  Freshness check before opening `APPROACHES.md` Approach 2's second wing (Yolcu–Aaronson–Heule string rewriting, machine-found certificates), which `DIRECTION.md` had rated "very low at present" and this repo never walked.  **The lane is active, and much of it is already barred by peers' theorems.**  It also contains a published open benchmark that fits our gates.  Peer clones: `~/src/peers/`.

## Peer work (all 2026, all public)

| Repo | Author | What it establishes | Tier |
|---|---|---|---|
| [harappa/collatz-termination-certificate-dichotomy](https://github.com/harappa/collatz-termination-certificate-dichotomy) (Part I, Zenodo [10.5281/zenodo.23081447](https://doi.org/10.5281/zenodo.23081447), r3 2026-10-02) | Hiroyuki Nashida | For generalized Collatz maps branching mod `2^k` into `(Ax+b)/2^e`: a terminating positivity-preserving map has a *staged valuation certificate* (log + 2-adic valuations at periodic points + finite-state weights) **iff** it is *disentangled* (no strongly connected component of the residue abstraction holds both an expanding cycle and a branching vertex).  For entangled maps, Collatz included, ranking functions computed from binary digits by positive, finite arctic, or non-negative automata with a primitive dominant block are excluded in every dimension. | Certificate soundness + 5 examples in Lean; the dichotomy and barriers are on paper |
| [harappa/collatz-matrix-interpretation-barriers](https://github.com/harappa/collatz-matrix-interpretation-barriers) (Part II, [10.5281/zenodo.23081491](https://doi.org/10.5281/zenodo.23081491)) | Nashida | Dimension-free barrier: no non-negative affine matrix interpretation with an exponentially growing primitive dominant block can drive YAH's relative-termination argument.  It also finds the maximal one-class weakenings of YAH Conjectures 4.11–4.14 that finite abstractions prove (e.g. a non-convergent orbit meets `5,7 mod 8` or `4089 mod 2^14`). | The seven weakenings are in Lean (`decide +kernel`); the barriers are on paper |
| [kadirbekov-ship-it/collatz-matrix-no-go](https://github.com/kadirbekov-ship-it/collatz-matrix-no-go) (Zenodo [10.5281/zenodo.22098492](https://doi.org/10.5281/zenodo.22098492), JAR submission) | Kadyrbekov & Kadirbekov | Unbounded 2-dim natural-matrix no-go.  `METHOD_LIMIT.md`: no bounded-horizon first-descent graph settles Collatz (`n_L = 2^(L+1)−1`).  `GLOBAL_ATTACK.md`: no `log₂ n + bounded P(n)` decreases at every step, and a finite-state factor with a well-founded quotient is already equivalent to Collatz. | Computer-assisted, Python |
| [Th0rgal/collatz-relative-termination](https://github.com/Th0rgal/collatz-relative-termination) | Th0rgal | SAT/GPU campaign for a single relative-termination certificate (natural/arctic/tropical).  As of 2026-07-25 the checker had accepted nothing.  Dimension one is impossible. | Campaign; no theorem |

## What this does to our maze

- **Our "2-adic adversary" gate is their published barrier.**  `BoundedMerger` (2026-09-29) and Kadirbekov's `METHOD_LIMIT` are the same Terras–Everett observation.  Treat the agreement as independent verification, and cite them rather than claim it.
- **Correction to [REVIEW-2026-09-29-ordinal-repair-odds.md](REVIEW-2026-09-29-ordinal-repair-odds.md).**  It said a locally computable rank was "not excluded."  Nashida Part I excludes the automaton-computed digit ranks above (primitive dominant block, positive growth, any dimension).  Kadirbekov excludes every `log n + bounded correction`.  The door that remains open is narrower: a rank that grows without bound relative to `log n`, or that is computed by a non-primitive/unbounded device.
- **The rewriting wing as a Collatz proof route is mostly closed by peers.**  Richer matrix interpretations of the 11-rule system fall under Nashida Part II.  We do not open a certificate-search campaign there.

## The target this hands us: Nashida's open entangled benchmark

Part I, §11, publishes `computations/maps_G2_open.tsv`: **4389 maps in `G_2` (mod 4, multipliers `A ∈ {1,3,9}`)** that are entangled, so no staged certificate exists.  On every start `x ≤ 500` they neither cycle nor escape within 5000 steps.  204 have two non-halting residues and 4185 have three.  Nashida explicitly proposes the list as a benchmark.  Each map is a toy Collatz whose termination is open.  **Proving termination of any one is a theorem beyond the dichotomy barrier**, so it needs a mechanism that consumes the map's arithmetic.  That is exactly the kind of mechanism our sibling-map gate demands.  It also has a finish line, and the community has asked for it.

Example (row 1, `0:1,-1,0;1:1,1,0;2:9,-2,2`, residue 3 halts).  Accelerated onto `x = 4a+2`, every surviving step is expanding: `a ↦ (9a+2)/4` for `a ≡ 2`, `a ↦ (9a+3)/4` for `a ≡ 1 (mod 4)`, and the other classes halt.  A non-halting positive orbit grows like `(9/4)^n` while its residues stay in an allowed set.  This is a **Mahler 3/2-type** question, `9/4 = (3/2)^2`.

### Probes, in order (each cheap, each with a known-answer control)

1. **Canonicalize and accelerate.**  Collapse `e = 0` branches and affine conjugacies, compose through forced residues, then re-run the dichotomy classifier on the accelerated map at the refined modulus.  If an accelerated map is disentangled and terminating, its staged certificate proves the original map terminates.  Nashida's `halts_of_cert` then checks it in Lean for free.  Control: Nashida's own disentangled `G_2` terminators must keep their category.  Either outcome is informative: some maps fall, or entanglement is stable under acceleration.  We need that answer before any harder work.
2. **Split the survivors by branch type.**  In the all-expanding subclass, a non-halting orbit is `ξ (p/q)^n` plus a bounded perturbation, with residues confined to a set.  Candidate mechanism: Flatto–Lagarias–Pollington (any `ξ > 0` has `limsup − liminf {ξ(p/q)^n} ≥ 1/p`) and Dubickas's perturbed extensions.  If the allowed residues force the fractional parts into too short a window, the map terminates.  **Prior art to read first:** Dubickas, *A Class of Bounded Iterative Sequences of Integers*, Axioms 13 (2024) 107, which cites YAH.  Confidence that at least one benchmark map falls to an FLP/Dubickas argument: 30%.
3. **Mixed maps** (some contracting branches) are Collatz-shaped in miniature.  Grade them only after 1–2.

**Gate.**  Before any Lean lap, run `papers followups` on both Zenodo DOIs (they are a week old) and check Nashida's repos for issues/updates.  Outreach to Nashida (the paper invites benchmark results) waits for a first theorem.  Per `docs/notes/` convention, Ren writes the note and Trevor writes the intro.

## Outcome, same day

**Probe 1 (canonicalize and accelerate) dropped.**  Nashida's dichotomy says no certificate exists for an entangled map, even with arbitrary bounded corrections, so re-running his classifier on simplified maps is almost certainly something he has already ruled out (Trevor's call, ~75%).

**Probe 2 (FLP) closed on the whole benchmark.**  `experiments/g2_mahler_triage.py triage maps_G2_open.tsv`:
- 226 of the 4389 maps are single-ratio (185 at 9/4, 26 at 9/2, 15 at 3/2).  The other 4163 mix ratios or have contracting branches, so FLP does not apply to them.
- None is excluded.  The best covering arc is 2/p, twice the FLP threshold.  Arcs that wrap through 0 are covered too, via Dubickas's shifted bound.
- Reading: entanglement means at least two allowed continuations inside an expanding component.  FLP's single short window is effectively the no-branching case, which is exactly the disentangled maps Nashida already settles.  This is a heuristic explanation; it is not proved for all maps.  My earlier 30% was miscalibrated.

**Mahler's 3/2 problem is inside the benchmark.**  Row `0:3,0,1;1:3,1,1;2:3,0,1` (line 1248, `INF-open`) is Mahler's 1968 recursion `g(x) = ⌈3x/2⌉`, halting at `x ≡ 3 (mod 4)`.  Sources: Mahler 1968, doi:10.1017/S1446788700005371, eqs. (2), (11), (13); Dubickas–Mossinghoff 2009, doi:10.1090/S0025-5718-09-02211-X.
- A Z-number forces an infinite `g`-orbit.  The converse fails: Mahler calls the condition "necessary (but not a sufficient)", and the real condition also forbids parity words such as `10101` (`1 + (2/3)² + (2/3)⁴ = 133/81 > 3/2`).
- So **termination of this benchmark map implies Mahler's conjecture**.  It is also implied by Dubickas's complexity conjecture (Glasgow Math. J. 51, 2009) and by the normality Conjecture 1.2 of Andrieu–Eliahou–Vivion, arXiv 2510.11723.
- Neither Nashida paper mentions Mahler, Z-numbers, FLP or Dubickas (both r3 PDFs read).  Lagarias's annotated bibliography, entry 117, states the correspondence as "if and only if", which overstates Mahler.

Lean statement staged: `KICKOFF-2026-10-05-mahler-benchmark.md`.  Outreach shape: Ren writes a `docs/notes/` note once the Lean statement lands; Trevor writes a brief intro to Nashida.
