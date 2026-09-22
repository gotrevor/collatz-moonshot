# Orbit packing makes the logarithmic correction summable

Second pass following `RESEARCH-2026-09-22-angular-clock.md`.
Paper proofs throughout; no new Lean theorem is claimed.

## Outcome and provenance

For a hypothetical divergent positive Collatz orbit:

1. Its values have a uniform power-saving packing bound in every interval.
2. The sum of their reciprocals is finite, with a uniform high-floor tail bound.
3. The cumulative logarithmic correction from +1 converges.  The odd
   logarithmic phases asymptotically track ONE irrational rotation.
4. The homogeneous coefficient tends to infinity, not merely along a
   subsequence.  Arbitrarily late tails are coefficient-supercritical forever.
5. Consequently `CrossingExists` is equivalent to absence of divergence.
   It permits positive cycles and does not require `StoppingCorrect`.

The packing mechanism is classical, not a new discovery.  Primary source:
M. V. P. Garcia and F. A. Tal, *A note on the generalized 3n+1 problem*,
Acta Arithmetica 90 (1999), 245-250,
[publisher PDF](https://matwbn.icm.edu.pl/ksiazki/aa/aa90/aa9033.pdf).
The whole six-page paper was read.  Their Proposition 1, equation (6), and
Corollary 1 contain a power-saving interval estimate behind the stated
Banach-density-zero conclusion.  The following proof replaces their
Heppner input with explicit elementary parity counting and gives its own
constants.  The deductions about summability and the conjecture graph are
spelled out here, without a priority claim.  Banach density zero ALONE
would not imply summability; the quantitative estimate is essential.

## 1. The collision-free object

Use the shortcut map T(n)=n/2 for even n and (3n+1)/2 for odd n.
Let O be the value set of an infinite positive orbit.  Every time-indexed
value is distinct: one repeat would imply eventual periodicity and a
finite orbit.  More strongly, T^m is injective on O for every m>=0.
Indeed, if T^i(n)!=T^j(n) but their m-step images agree, the original
orbit repeats at times i+m and j+m.

This is where an actual single integer orbit is used.  A large set of
arbitrary starts need not have this collision-free property.

## 2. Explicit packing in aligned blocks

Fix m>=0 and an aligned block [q*2^m,(q+1)*2^m), q>=0.
Write each integer in it uniquely as q*2^m+s with 0<=s<2^m.
Let r(s) be the number of odd steps in the first m shortcut steps of s.
Parity reconstruction and the affine iterate identity give

    T^m(s+q*2^m)=T^m(s)+q*3^r(s).                         (1)

There are exactly binomial(m,r) residues with r(s)=r.  The parity-word
bijection follows inductively: extending a word chooses one of the two
lifts modulo 2^(m+1), since its odd multiplier is invertible modulo 2.

For odd positions p_0<...<p_(r-1) in the word,

    numer = sum_{j<r} 2^p_j * 3^(r-1-j)
          <= 2^(m-r) (3^r-2^r),

because p_j<=m-r+j.  Hence

    0 <= T^m(s) = (3^r*s+numer)/2^m < 2*3^r.              (2)

Partition the block at r=3m/5.

GOOD residues have r<=3m/5.  For a FIXED r, (1)-(2) put all their
images in an integer interval with at most 2*3^r elements.  Injectivity
on O bounds their number by that quantity.  Summing over at most m+1
possible values of r gives at most 2(m+1)*3^(3m/5) orbit elements.

BAD residues have r>3m/5.  Their total number, whether or not in O, is
bounded by the binomial generating function at t=3/2:

    sum_{r>3m/5} binomial(m,r)
      <= (3/2)^(-3m/5) (1+3/2)^m = nu^m,
    nu^5 = 3125/108.

Take lambda=63/32.  Both 3^(3/5) and nu are less than lambda, since

    27 * 33554432 = 905969664 < 992436543 = 63^5,
    3125 * 33554432 = 104857600000
                    < 107183146644 = 108 * 63^5.

Thus the aligned-block bound is

    # (O intersect [q*2^m,(q+1)*2^m)) <= (2m+3) lambda^m.  (3)

The constants are deliberately not optimized.  The saving exists because
1/2 < 3/5 < log_3 2: typical parity words contract, and atypical words are
exponentially few.  This is not a claim that the particular orbit has
typical parities.  We count the orbit's POSSIBLE distinct images instead.

## 3. Uniform intervals and reciprocal tails

Set

    beta=log_2(63/32) < 1,
    eta=1-beta=log_2(64/63) > 0.

An interval of integer length X>=1 meets at most two aligned blocks of
length 2^m with m=ceil(log_2 X).  Since m<=log_2 X+1 and
lambda^m<=lambda X^beta, (3) gives the convenient bound

    # (O intersect [a,a+X)) <= 20(1+log_2 X) X^beta         (4)

uniformly in nonnegative integer a.  It also bounds any subset of O.

For an integer floor F>=1, split values >=F into dyadic shells of lengths
2^j F.  Equation (4) gives

    sum_{x in O, x>=F} 1/x
      <= 20 F^(-eta) sum_{j>=0} (1+log_2 F+j)(63/64)^j
      = 1280 F^(-eta)(64+log_2 F) =: B(F).                 (5)

Here sum rho^j=64 and sum j rho^j=4032 for rho=63/64.
In particular B(F)->0, and the full reciprocal sum is finite.
These crude constants are not useful at the current verification frontier;
the conclusion needed here is uniform decay as F->infinity.

Time-indexed and set sums agree only because the divergent orbit is
injective.  A periodic orbit has a finite value-set reciprocal sum but an
infinite TIME-indexed reciprocal sum.  It is not covered by this argument.

## 4. A convergent logarithmic correction, with a uniform remainder

For an odd-to-odd orbit x_i write

    x_(i+1)=(3x_i+1)/2^a_i,
    A_i=sum_{j<i}a_j,  alpha=log_2 3,
    E_i=sum_{j<i} log_2(1+1/(3x_j)).

By (5), E_i increases to a finite E_infinity.  The exact product identity
now yields an asymptotic expansion on the REAL line, not just modulo 1:

    log_2 x_i = i alpha - A_i + Phi - R_i,
    Phi=log_2 x_0+E_infinity,
    R_i=E_infinity-E_i > 0,  R_i->0.                       (6)

If every future orbit value from time i is at least an integer F, then

    R_i <= B(F)/(3 log 2).                                (7)

Thus the phase is asymptotic to one specific irrational rotation
i alpha+Phi.  The first paper proved only equidistribution from vanishing
per-step error; (6) supplies convergence of the accumulated error itself.

In shortcut notation, let y_k=T^k(n), r_k be its odd-step count, and

    b_k=3^r_k/2^k,
    P_k=product_{j<k, y_j odd} (1+1/(3y_j)).

Then y_k=n b_k P_k, with 1<=P_k increasing to finite P_infinity.
Since divergence makes y_k->infinity, it follows that

    b_k->infinity,
    k log 2-r_k log 3 -> -infinity.                        (8)

This improves the old route note's liminf-only conclusion.  No lower
growth rate in time is asserted; late excursions back to smaller scales
are not ruled out by a bound on the number of values in an interval.

## 5. CrossingExists is exactly the divergence front

Recall the EXISTING definition from `FrontA/FirstCrossing.lean`:

    CrossingExists := forall n>=2, exists m, 3^r_m < 2^m.

Claim, for positive 3n+1:

    CrossingExists <=> every positive orbit is bounded.    (9)

Forward implication: suppose a divergent orbit exists.  By (8), b_k
tends to infinity.  It therefore attains a minimum on every index tail
{k:k>=j}.  Choose a minimizing k_j>=j.  For every t>=0,

    3^(r_(k_j+t)-r_k_j)/2^t = b_(k_j+t)/b_k_j >= 1.

The positive integer y_(k_j) is consequently a ballot-forever start.
It is >=2 (a divergent orbit cannot hit 1).  This contradicts
CrossingExists.  Letting j grow also proves the existence of arbitrarily
late ballot-forever tails in every hypothetical divergent orbit.

Reverse implication: a bounded positive integer orbit is eventually
periodic.  On a positive cycle, some step is odd: a nonempty all-even
cycle would strictly decrease.  The exact product identity around the
cycle says 1=b_period P_period, where P_period>1 because of that odd
step.  Thus b_period<1.  Repeating the period makes the full prefix
coefficient tend to zero, regardless of the finite preperiod.  It must
eventually cross below 1.  This proves CrossingExists.

This is an equivalence of GLOBAL statements.  A divergent orbit need not
be ballot forever at its original starting point; it has a tail with that
property.  Positive nontrivial cycles, if any exist, satisfy CrossingExists.
No assertion about descent at the FIRST coefficient crossing was needed.

Consequently the clean full-conjecture split is

    Collatz <=> CrossingExists AND NoNontrivialCycle.

The existing sufficient split with StoppingCorrect remains valid, but
StoppingCorrect implies cycle exclusion; its converse is not established.
The proof of (9) is paper-level here; existing Lean declarations have not
been silently changed or claimed discharged.

## 6. A retired-looking intermediate target has full strength

The old Route A2 discussion proposed an infinite reciprocal budget along
every divergent orbit as a possible ingredient in moving-tail aggregation.
Equation (5) proves the opposite under the divergence hypothesis.
Accordingly the conditional statement

    forall divergent orbits, sum_k 1/T^k(n)=infinity

is EQUIVALENT to absence of divergent orbits: if it held, (5) would give
a contradiction; if no divergent orbits exist, it is vacuous.  It is not
legitimate to label that conditional statement outright false without an
actual divergent orbit.  It is a full-strength target, not an intermediate
lemma available from divergence.  This correction does not refute every
possible packing or saturation mechanism.

## 7. What the logarithms still do not give

The real constant Phi in (6) is orbit dependent.  We have not proved it
algebraic or related it to a fixed known constant.  A lower bound for
linear forms in log 2 and log 3 alone does not control an arbitrary
inhomogeneous shift Phi.

Moreover phase closeness is RELATIVE height closeness.  At a future
minimum x_i=F, (7) permits an absolute height error of order
F^(1-eta) log F, not an error below one integer spacing.  Rounding a
shadow height to an integer is therefore unjustified.

A simple explicit control retains even stronger shadowing.  Put

    x_i=(31/10)(3/2)^i-1.

It obeys x_(i+1)=(3x_i+1)/2, starts at 21/10, is positive, injective,
and diverges exponentially.  Its reciprocal sum converges.  The interval
count is O(log(2+X)) uniformly in the interval position, since successive
gaps increase geometrically.  It satisfies (6) with

    Phi=log_2(31/10),  R_i=log_2(1+1/x_i),

so its ideal shadow differs from x_i by exactly 1.  Yet its denominators
are 5*2^(i+1), with no cancellation, and it is never an integer orbit.

For a positive INTEGER initial value n, the same all-a_i=1 formula can
remain integral only while 2^i divides n+1.  This elementary case shows
exactly where integrality bites.  Extending that exclusion to variable
valuation words is the unresolved step, not something (6) proves.

## 8. Controls and research assessment

- The DISTINCT values of a pure cycle also have injective T^m, so the
  packing bound applies to them too.  What fails for a cycle is the passage
  from a set sum to an infinite time-indexed sum: time repeats its values.
  In particular a primitive cycle with minimum F and K odd members obeys
  0<A log 2-K log 3<=B(F)/3, by summing the correction once around the
  cycle.  This bound is independent of its period, but does not exclude
  arbitrarily close logarithmic resonances.  Positive cycles are also
  included in the reverse implication of (9).
- The negative-sign 3n-1 cycle through 5 does not contradict the result:
  its period correction is less than one, so the reverse implication's
  positive-cycle argument changes sign.  Do not generalize (9) to 3n-1.
- The 5n+1 control does not support the packing proof: no threshold p
  satisfies 1/2<p<log_5 2.  The new packing input genuinely consumes the
  multiplier-3 entropy deficit, without assuming random parities on O.
- The first paper's linear-growth rational control has infinite harmonic
  budget; (5) now rules out that behavior for actual divergent integer
  orbits.  The exponential rational control above survives the strengthened
  real constraints and still fails exact integrality.

This pass repairs a real gap in the project's mathematical map and gives
a stronger arithmetic-derived shadow law.  It does NOT prove
CrossingExists, exclude many-run cycles, or provide a new uniform residue
lower bound.  No unattended proof lap is authorized by this note.
