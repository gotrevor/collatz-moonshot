# Review: ordinal repair, and the odds of closing it

Reviewer: Ren (Opus 5.5), at Trevor's request.  Scope: [the ordinal-repair checkpoint](RESEARCH-2026-09-29-ordinal-repair-checkpoint.md), [the bounded smaller-merger obstruction](RESEARCH-2026-09-29-bounded-small-merger.md), and the 2026-09-29 notes they cite.  Evidence tiers are as those notes state them; this review re-ran no build.

## Difficulty check

- **Proved implications.**  A signed integer flow with boundary `e_n - e_1` is equivalent to convergence (`SignedFlow.lean`).  Applegate–Lagarias supplies arbitrary finite 3-free catalysts (literature).  Multisets of pending smaller obligations carry an ω^ω rank, which is strong induction.  Universal return-or-target-terminal coverage on the uncovered hard progression implies full Collatz via Monks' sufficiency theorem (literature, not Lean).
- **Unproved premise.**  Every non-terminal state of some closed class admits a completed block that lowers a full-state rank.  By [the coverage audit](RESEARCH-2026-09-29-ray-coverage-difficulty.md) this is equivalent to convergence on an infinite arithmetic progression, hence to the conjecture.
- **Mechanism for the premise.**  None known.

## What the day established

Positive results: the variable cubic continuation (`CubicPeel.lean`, infinite class with unbounded initial growth), the Q1 18-step descent class, the signed-flow equivalence, and the supply correction (the restricted palette is not a prerequisite).  Every other 2026-09-29 result closes a template: coefficient-only ranks (the ray), fixed-depth splices into `q1`, the bounded post-cubic gap, fuel refill, and bounded-depth merger with any smaller seed.

The obstructions share one locus.  Each is built from 2-adic congruence classes (in `BoundedMerger`, 2-adic and 3-adic) that prescribe a long parity prefix.  By the Terras–Everett bijection every finite parity prefix is realized by a residue class, so any rule that reads a bounded amount of the orbit leaves an infinite class uncovered.  `BoundedMerger` states this once, globally, for every smaller seed; that is its value.  It retires fixed-depth menus as a class instead of one family at a time.  It makes no novelty claim, and its elementary proof suggests the statement may be folklore.

The rank side points the same way.  On fresh normalized states the candidate weight is `8d^4`, so a lower reset weight is equivalent to a smaller `d` ([run macro](RESEARCH-2026-09-29-q1-run-macro.md)); that template supplied nothing beyond numerical descent.  A rank that decreases across adaptive-depth blocks has to carry information about the orbit's future.  The obvious such rank is the stopping time, which is what the proof is trying to establish.

## Where the Goodstein analogy breaks

Goodstein's rank is read locally off the hereditary base representation, and its decrease is a one-step check.  Its proof-theoretic height (ε₀) is what places it beyond PA.  Here the height is free (ω^ω suffices), and the local reading is exactly what `BoundedMerger` and the Q1 separation exclude.  The analogy needs a finite representation of `n` whose rank decreases at every step; no candidate exists.

## Missing control

A grep of the 2026-09-27..29 notes found no test of the certificate-repair framework on a map where the answer is known to be negative.  The candidates are 3x+1 on negative integers (cycle -5, -7, -10) and positive 5x+1 (cycle 13, 33, 83, 208, 104, 52, 26).  The pairwise branch already uses both (`pair-denominators`, `pair-ordering`, `pairwise-crossing-audit`).  Before any further rank candidate, state the repair framework's analog for both maps:

- If supply and the local exchanges transfer, any proposed rank must fail on the analog, and the step where it fails names the 3x+1-specific input the real proof must consume.
- If supply does not transfer, that difference is the first 3x+1-specific lever this branch has found.

## Closing sketch

Conditional probabilities; horizon is the life of this project.

| Step | Content | P |
|---|---|---|
| 0 | Reformulation, supply, well-foundedness | done |
| 1 | Sign/map control run and informative (diagnostic, not on the critical path) | 70% |
| 2 | A closed full-state class with a non-circular variable-depth block rule, defined without simulating the orbit to termination | 20% |
| 3 | Coverage and decrease: every non-terminal state admits a block that lowers the full-state rank | ≤ 0.1% |
| 4 | Terminal condition and assembly through `SignedFlow` | 90% |
| 5 | Lean formalization of the whole | 80% |
| **Close** | product of steps 2–5 | **≈ 0.01%** |

Step 3 is the conjecture; steps 2, 4 and 5 are research engineering.

## Recommendation

Run step 1 once.  Unless it exposes a 3x+1-specific lever, record the repair branch's closed templates as a closed route and stop generating template obstructions.  Twenty-one research notes dated 2026-09-29 each closed one template, and the next will close the same way for the same reason: a bounded reading of a 2-adically adversarial orbit.  The checkpoint's own gate already says this; this review adds the control and the odds.
