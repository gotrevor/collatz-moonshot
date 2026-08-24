# Niu 2026: parity vectors and paradoxical sequences

Primary source: Tong Niu, *Parity vectors and paradoxical sequences in the accelerated
Collatz map*, arXiv:2605.13886 (submitted 2026-05-11),
<https://arxiv.org/abs/2605.13886>.

## Scope

The preprint builds on Terras/Everett parity-vector equidistribution and
Rozier--Terracol's paradoxical sequences. Its abstract reports three unconditional results:

1. a sharp finite form of parity-vector density;
2. a closed-form analytic count of paradoxical segments at each fixed length;
3. density zero, with an explicit constant, for paradoxical segments of bounded length.

These are source-lock baselines for `FRONT-A-PARADOXICAL.md`, not new targets to rediscover
in Lean unless a proof component is needed by a genuinely new result.

## Conjectural numerical pattern

For the seven `(j,q)` pairs in the Rozier--Terracol enumeration with start `n≤10^9`, the
paper observes that every reduced ratio `q/j` belongs to a small continued-fraction family
for `log_3 2`: a left convergent, a left semiconvergent, or a specified Stern--Brocot mediant
of adjacent convergents/semiconvergents. The reported ratios include the familiar near-left
approximations `5/8`, `17/27`, `29/46`, and `41/65`, with `46/73` appearing through the
mediant mechanism.

This classification is numerical/conjectural. It is an excellent falsification target:
test it with exact rationals and preserve the smallest counterexample. More finite support
does not prove it, and the paper itself makes no claim toward Collatz or the
coefficient-stopping-time conjecture.
