# Self-packing bootstrap: an exact stopping threshold

Paper exploration, 2026-09-22.  This is a rejected exclusion mechanism,
not a Collatz breakthrough or a literature-priority claim.

## Question

Can the packing estimate reinforce itself until an infinite orbit becomes
impossible?  The image of a segment is in the same orbit, so its count also
satisfies the orbit's existing interval bound.

Let O be an infinite positive shortcut orbit.  Every T^m is injective on O.
Assume, uniformly in interval position, that

    #(O intersect I) <= C X^d

for integer intervals of length X>=1, with 0<d<=1.  Write alpha=log_2 3.
The elementary starting bound has d=1.  The preceding packing note supplies
a stronger starting bound, with an arbitrarily small power absorbing its log.

## Bootstrap calculation

In [q 2^m,(q+1)2^m), partition starting values by their odd count r in m
steps.  There are exactly binomial(m,r) residue classes with that count.
The affine identity gives

    T^m(q 2^m+s)=q 3^r+T^m(s),  0<=T^m(s)<2*3^r.

Injectivity and the assumed interval bound therefore give

    count_r <= min(binomial(m,r), C 2^d 3^(dr)).

For binary entropy H(p)=-p log_2 p-(1-p)log_2(1-p), with endpoints
defined by continuity, binomial(m,r)<=2^(m H(r/m)).  Consequently the
aligned-block count is at most

    max(1,C 2^d)(m+1) 2^(m F(d)),
    F(d)=max_{0<=p<=1} min(H(p),d alpha p).

Cover an arbitrary length-X interval by at most two aligned blocks of the
smallest dyadic length >=X.  It follows that every exponent strictly above
F(d) is another valid uniform interval exponent.  Constants may change.
This is a finite bootstrap, not a justification for taking a limit of the
constants or asserting a bound at the limiting exponent.

## Why it stops

On [0,1/2], the minimum is d alpha p, because H(p)>=2p and d alpha<2.
On [1/2,1], entropy decreases and d alpha p increases.  Thus their unique
intersection p_d in (1/2,1) gives F(d)=d alpha p_d=H(p_d).
Set

    p_*=1/alpha=log_3 2,
    d_*=H(p_*).

For d>d_*, the intersection lies below p_*, and F(d)<d.  But evaluation
at p_* gives

    F(d) >= min(H(p_*),d alpha p_*) = d_*.

At d=d_* there is equality F(d)=d_*.  For 0<d<d_*, the intersection lies
above p_*, giving F(d)>d, a weaker bound than the input.

Iteration from d=1 therefore approaches d_* from above, never zero.
More precisely, continuity and the unique positive fixed point show that
the ideal iterates decrease to d_*; allowing sufficiently small exponent
losses proves each fixed target exponent greater than d_* after finitely
many steps.  Nothing here proves a bound with exponent exactly d_*.

The critical population r/m=log_3 2 survives this particular estimate:
its image interval has the same exponential scale as its source interval.
The available binomial population has exponent d_*, while self-packing
with input d>=d_* permits at least that exponent.  These are capacities
in an upper-bound argument, NOT a construction of a realizable orbit.

## Verdict and scope

This scalar, separate-fibre bootstrap cannot yield an exclusion.  Its
limitation does not apply to joint fibre constraints, composition-sensitive
estimates, or additional arithmetic information.  In particular it is not
an optimality theorem for all orbit packing methods.  Do not open a proof
lap merely to formalize this improved exponent as if it closed the crux.

## Prior work checked during this pass

Read-only peer checkout: https://github.com/msharpe248/collatz at
ec8174b567d5cab4960024782210b5f5db02bd3a.

- paper/noncontracting_tails.tex already states the global equivalence of
  boundedness and eventual coefficient contraction, using summability.
  Its Lean implementation is reported there; it was not rebuilt here.
- paper/ideal_tracking_barrier.md proves an ideal-shadow gap greater than
  one and an even-tail gap greater than two.  This rules out promoting the
  tempting floor-of-shadow argument into a fresh exclusion mechanism.
- paper/correction_attainability.md distinguishes an arbitrary correction
  satisfying endpoint congruence from a correction attained by an actual
  parity word.  Its exact decoder is a criterion, not uniform exclusion.

These observations give provenance and prevent duplicate proposals.  They
do not independently verify every declaration or claim in the peer repo.
