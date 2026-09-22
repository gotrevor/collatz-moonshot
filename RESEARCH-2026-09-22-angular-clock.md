# An ordered logarithmic clock, and why its marginal law does not force descent

Follow-up: [packing and convergent logarithmic correction](RESEARCH-2026-09-22-packing-shadow.md)
uses actual integer-orbit collision avoidance to prove reciprocal summability.  This
strengthens the phase conclusion to tracking one rotation and rules out the linear-growth
rational control as a model of integer orbit packing.  The present real-relaxation
counterexamples remain valid within their stated scope.

Independent research following Trevor's request to create a new Collatz
mechanism.  These are paper proofs, not new Lean theorems.  No priority claim
is made.  No mechanism here clears the standing proof-lap gate.

## Starting point and scope

Read against `DIRECTION.md`, `APPROACHES.md`, `FRONT-A-ROUTES.md`,
`FRONT-B-ROUTES.md`, `RESEARCH-2026-09-22-mechanism-search.md`, and the
integer-spacing obstruction.  Relevant proved assets include
`Rigidity/Drift.lean` (injectivity and eventual floors of divergent orbits),
`FrontA/HarmonicMean.lean` (the reciprocal-sum drift bound), and
`FrontA/FirstCrossingResidue.lean` (primitivity and the overshoot congruence).

This does not reopen run-equation congruence harvesting, Christoffel residue
signatures, parity normality, or unweighted backward-density amplification.
The question tested is whether retaining the temporal order of *real
logarithmic phases* supplies information absent from scalar spacing bounds.

An important status distinction: the first-crossing few-run bound is 50 in
Lean under the stated verification hypothesis; 68 is the paper-level reach.
Neither the existing run-count lower bound nor a proposed linear improvement
of it would exclude the complementary many-run failures by itself.

## 1. Finite ordered Fourier estimate

Let x_0,...,x_K be positive real numbers satisfying

    x_(i+1) = (3 x_i + 1) / 2^(a_i),   a_i an integer.

For actual odd-to-odd Collatz iterates a_i=v_2(3x_i+1)>=1.  Define

    alpha = log_2 3,
    theta_i = log_2 x_i modulo 1,
    epsilon_i = log_2(1 + 1/(3x_i)),
    H_K = sum_{i<K} 1/x_i,
    e(t) = exp(2 pi i t).

The exact ordered recurrence is

    theta_(i+1) = theta_i + alpha + epsilon_i modulo 1.       (1)

For each nonzero integer h set D_h=|e(h alpha)-1|>0.  Irrationality
of alpha follows from unique factorization: 2^p=3^q is impossible for
positive integers p,q.  Then

    D_h |K^(-1) sum_{i<K} e(h theta_i)|
       <= 2/K + (2 pi |h| / (3 log 2)) H_K/K.                (2)

Proof: write z_i=e(h theta_i), q=e(h alpha), and telescope

    (q-1) sum_{i<K} z_i
      = z_K-z_0 - q sum_{i<K} z_i (e(h epsilon_i)-1).

Use |e(t)-1|<=2 pi |t| and 0<epsilon_i<=1/(3x_i log 2).
The endpoint term is essential.  For a complete cycle z_K=z_0, it is
exactly zero, not merely bounded by 2.  This establishes (2) without
independence, random parity, a density assertion about starting seeds, or
a sign-changing asymptotic approximation.

### Consequences with the quantifiers stated

1. A hypothetical divergent positive Collatz orbit has x_i->infinity
   along its odd iterates, by the existing injectivity/free-floor argument.
   Thus H_K/K->0.  For every fixed h!=0, (2) tends to zero.  Weyl's
   criterion gives uniform distribution of theta_i along this ONE orbit.
   Equivalently its odd iterates are Benford in base 2.  This is NOT
   normality of a parity word, and does not assert decimal Benford behavior.
2. For any sequence of finite orbit segments with lengths K->infinity
   and minimum values N->infinity, (2) is bounded by
   2/K + 2 pi |h|/(3 N log 2).  Their phase empirical measures tend to
   Lebesgue measure.  The statement is about this joint limiting regime.
3. For any hypothetical sequence of positive cycles whose odd minima
   N->infinity, the cycle phase measures tend to Lebesgue measure, even
   without assuming a period growth rate: the endpoint term vanishes.

The constants are frequency dependent through D_h.  No uniform-in-h
estimate or growing-frequency conclusion has been obtained.

## 2. A modest genuine improvement to a harmonic bound

For x>=N>0 put u={log_2 x-log_2 N}.  Since x/N=2^(j+u) with integer j>=0,

    N/x <= 2^(-u).

For either limiting regime in items 2-3 above, uniform distribution gives

    limsup (N/K) sum_{i<K} 1/x_i <= integral_0^1 2^(-u) du
                                  = 1/(2 log 2).            (3)

The translating phase log_2 N may vary: approximate 2^(-{t}) from above
and below by step functions, and use uniform interval discrepancy.  The
single jump causes no problem.  Thus (3) improves the naive coefficient
1 in H_K<=K/N to approximately 0.72135 in the specified limits.

For cycles, the same phase distribution also implies

    liminf max(x_i)/min(x_i) >= 2

along any family with minima tending to infinity.  Otherwise an arc of
fixed positive length in relative phase would contain no cycle values.

These are constraints, not a descent mechanism.  A constant-factor gain
in the reciprocal-sum estimate does not bridge the existing run-count or
full-admission barriers.  No claim of novelty relative to the literature
is made for (2), (3), or their corollaries.

## 3. Exact rational controls: the missing arithmetic can carry everything

Here is a constructive obstruction to upgrading the phase law plus real
recurrence, injectivity, and eventual floors into non-divergence.

Choose a nondecreasing rational envelope L_i>=1, tending to infinity, with

    2 L_(i+1) <= 3 L_i + 1.

Start with x_0 in [L_0,2L_0).  Given x_i define

    a_i = floor(log_2((3x_i+1)/L_(i+1))),
    x_(i+1) = (3x_i+1)/2^(a_i).                             (4)

Inductively x_i is in [L_i,2L_i).  The ratio inside the logarithm is
at least 2 and strictly less than 8, hence a_i is always 1 or 2.
All x_i are rational when the envelope and initial value are rational.
The exponent can equivalently be chosen by exact rational comparisons;
there is no numerical logarithm in this construction.

Take integer L_0 and x_0=L_0+1/10.  In lowest terms the denominator starts
as 10.  If it is 5*2^b with odd numerator p not divisible by 5, the next
numerator before reduction is 3p+5*2^b, again odd and not divisible by 5.
The next denominator is 5*2^(b+a_i).  Therefore every value is nonintegral,
and denominators strictly increase, so the sequence is injective.

Two concrete envelopes cover both reciprocal-budget cases:

- L_i=i+2.  Then sum 1/x_i diverges, since x_i<2(i+2).
- L_i=(i+5)^2.  The envelope condition follows from
  t^2-4t-1>=0 for t>=5.  Then sum 1/x_i converges, since x_i>=(i+5)^2.

For the first envelope the first five values, by exact substitution, are
21/10, 73/20, 239/40, 757/80, 2351/320.  The chosen exponents are
1,1,1,2.  These are algebraic anchors, not a census of integer orbits.

Both constructions have exact +1 affine dynamics, a_i in {1,2},
injectivity, every eventual floor, divergence, and the phase law (2).
Neither is an orbit of the accelerated Collatz map on odd integers.
In particular a_i is NOT asserted to be a 2-adic valuation.  That is the
arithmetic condition the control deliberately removes.

Thus this is a counterexample to the stated REAL relaxation, not to any
integer Collatz conjecture, and not to a method using exact parity admission.
Splitting the route according to convergence of sum 1/x_i does not repair
this relaxation: both sides have explicit divergent controls.

The sibling controls also locate the scope.  Replacing 3 by 5 gives the
same calculation with alpha=log_2 5 and the corresponding error constant;
it does not exclude the known 5n+1 cycles.  Replacing +1 by -1 changes the
sign of epsilon and bounds its absolute value by 1/((3x_i-1) log 2).
The 3n-1 cycle through 5 has a fixed small floor, so it does not satisfy
the divergent-orbit hypothesis or the large-minimum limiting hypothesis.
Consequently the new clock supplies no sign-specific exclusion by itself.

## 4. Averaging obstruction to an independent angular certificate

Another tempting use of the clock is to add theta to the existing finite
residue/height-state backward-tree potential.  The following exact lemma
limits that proposal.

Let S be finite.  For each state s and admissible choice u let there be a
finite list of edges (t_e,w_e,beta_e), where w_e>=0.  Suppose integrable
functions V_s(theta)>=c>0 satisfy, for every theta and every choice u,

    sum_e w_e V_(t_e)(theta+beta_e) >= lambda V_s(theta).     (5)

Then v_s=integral V_s(theta) dtheta are positive and satisfy

    sum_e w_e v_(t_e) >= lambda v_s                         (6)

for every same choice u.  This follows just by translation invariance of
Lebesgue measure and integration of (5).  Conversely a vector satisfying
(6) gives constant functions satisfying (5).  Hence the achievable lambda
values are IDENTICAL.  A robust minimum over choices does not evade the
lemma: retain all the individual inequalities before integrating.

For a Collatz inverse odd branch y=(2^j x-1)/3, its angular increment is

    log_2 y-log_2 x = j-alpha+log_2(1-1/(2^j x)).

The high-height limiting angular shift is -alpha for every branch.  So
appending an independent circle coordinate to a limiting finite-state
certificate of shape (5) cannot improve its expansion factor.  This applies
to that precise product-state relaxation, not to arbitrary exact arithmetic
certificates.  A fixed Lipschitz angular correction has a vanishing error
as x->infinity; it cannot manufacture a fixed strict limiting margin.
Singular, height-dependent corrections or genuinely restricted joint state
spaces are outside this lemma and would need separate proofs.

## 5. Research verdict and the next constraint

The ordered logarithmic clock is real and gives quantitative necessary
conditions.  Its marginal equidistribution is not the missing mechanism.
The explicit rational controls and the averaging lemma explain two precise
ways a superficially promising extension loses all arithmetic leverage.

A surviving use of this coordinate must couple its real phase to the
*actual valuation choice*, not average the phase separately or assume an
independent residue/phase product.  Merely naming that coupling is not a
new lemma: a claim that it forces mean valuation above log_2 3 would be the
existing drift-rigidity target in different language.  No estimate proving
such a coupling has been obtained in this attempt.

Do not launch a formalization grind on the strength of these necessary
conditions.  In particular do not describe this as progress excluding a
divergent integer orbit or a many-run cycle.  Preserve the finite inequality
and controls as a screen for the next genuinely arithmetic proposal.

## Literature calibration

Benford behavior in Collatz has an established literature.  The abstract of
[Lagarias-Soundararajan, math/0509175](https://arxiv.org/abs/math/0509175)
states approximate Benford behavior for the first N iterates of *most seeds*.
[Kontorovich-Miller, math/0412003](https://arxiv.org/abs/math/0412003)
also studies a statistical Benford formulation.  Their abstracts were
checked here to avoid claiming the general direction as new.  They are not
being cited as proofs of the individual-orbit conditional statements above;
those follow from the displayed telescoping calculation.  This was not an
exhaustive priority search.
