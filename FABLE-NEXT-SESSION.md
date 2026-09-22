# Fable: a mechanism search, not another rung campaign

Prepared 2026-09-22 by Ren/Codex for Trevor's requested next-session plan.
Read DIRECTION.md's top section and retired list, APPROACHES.md,
FRONT-A-ROUTES.md, and PROBE-2026-09-20-carry-budget.md.
No Collatz execution lap has been launched by this brief.

## First question: does the selected node buy the claimed conclusion?

The current run-count goal asks for r>=epsilon*K on a hypothetical
first-crossing failure.  That would be a substantial improvement over
logarithmic run bounds, but a linear LOWER bound on runs alone does not
exclude a many-short-runs failure.  Demand the exact remaining implication
to StoppingCorrect.  Do not call an intermediate bound equivalent to CST
without a proof.  Quantifier auditing is justified here by the concrete
false PrefixDecay input found in NN during this planning session.

The exact mathematical target remains full admission: for a ballot word v,
D=2^m-3^K>0, N=numer(v), realizing residue
r=[-N*(3^K)^(-1)] mod 2^m, a failed first-crossing descent requires
a realizing n>=2 with D*n<=N.  Preserve the equality/cycle boundary.
Equivalently D*n+2^m*E=N with an integer E>=0 and the small overshoot bounds.
Any new condition must exclude actual admitted starts, not rational cycles
or only a fixed number of residue bits.

## Two research rounds, independent of each other's optimistic narrative

A. Arithmetic mechanism: inspect the exact run-to-run admission equations
and identify an amortized constraint across a VARIABLE number of runs.
What information is lost when separate run bounds are multiplied?
A candidate must use jointly realizable states and supply an inequality
or invariant with a proof attempt.  An average over random words is not a
uniform bound.  Finite-window bounds are not enough merely because the
window is larger than last time: show how the window length scales.

This is a question, not a proposed new mechanism already known to work.
The old two-run Mersenne congruence and base3-digit-window obstruction are
known.  Repeating them is not an answer.  Require a new load-bearing step,
or report that this round did not find one.

B. Adversarial/global alternative: independently inspect whether a
positive-integer orbit constraint can control admission or CrossingExists
without assuming normal parity, positive entropy, or backward-density
amplification through a fixed seed.  These routes have explicit failures
in the repo.  A proposed replacement must state which failed premise is
replaced, by what provable claim, and why actual positive integers satisfy it.
No new conditional wiring unless it consumes genuinely weaker input.

## Tests before any helper launch

- Trivial 1/2 cycle and n>=2 boundary; negative cycles as sign controls.
- The retired rational short-run families and the P6-passing family.
- Orbit27 and recorded near-misses; the 2305/2313 prefix-remainder pair.
- The Mersenne q=12,next-run=6 example; no small-scan universal inference.
- Word powers/repetitions: no hidden equivalence to the whole conjecture.
- Scaling: what happens with K growing and r proportional to K?
- Does the proof use positivity/integrality, or would it falsely exclude
  known 3n-1 cycles?  Divergence-only claims need not exclude those cycles.

Use the existing parity_reconstruction.py and carry_budget.py instruments
only when a candidate predicts a NEW measurable distinction.  Reuse their
tests and persist new controls; do not launch a bigger census by default.
The carry-budget null is finite evidence against that proposed statistic,
not a theorem excluding all global carry arguments.

## Launch gate and deliverables

DIRECTION's no-lap-without-a-mechanism gate stands.  A Fable research round
is not an Opus formalization campaign.  A survivor must supply:
an exact statement; novelty versus retired approaches; a load-bearing
proof step; predicted controls; and a path from it to a named frontier.
Then Opus/low can implement a bounded theorem or falsification task.

Allocate multiple fresh adversarial attempts before investing in a long
proof, but retire a repeated failure instead of renaming it.  A successful
day can be a new mechanism or a rigorous exclusion of a plausible one;
it need not be a promised Collatz breakthrough.
No r=51..68 port, no fixed-prefix revival, no constant tightening, no
automatic-set restatement, no probabilistic residue assumption.
