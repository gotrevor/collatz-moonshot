# Finite temporal packing excludes the linear-size Christoffel candidates

Paper proof, 2026-09-22.  Uses the classical packing mechanism now implemented
in OrbitPacking.lean.  This finite-segment application is not yet formalized;
no literature-priority claim is made.  It excludes nonrepeating realizations,
not all realizations, and does not prove either Collatz front.

## Result

Let v_K be the recorded first-crossing word whose odd positions are
p_i=floor(i log_2 3), 0<=i<K, with total length m=p_K+1.
For every fixed C>0, for all sufficiently large K:

    No positive integer n<=C K realizes v_K with its K odd states distinct.

Consequently, any such actual realization must repeat an odd state within the segment,
and consequently its orbit is eventually periodic.  For the exact interval
[10K,12K] used in the mixed-prefix obstruction, the explicit, deliberately
unoptimized sufficient threshold K>=2^1280 works.

Thus finite temporal packing rejects those candidates AS NONREPEATING
TRAJECTORIES, although they pass exact short-prefix admission and optimal
unordered tail spacing.  It does not decide the repeated-state branch.

## 1. A finite-segment packing lemma

Write T for the shortcut map and x_i=T^i(n).  Suppose x_0,...,x_L are
pairwise distinct.  Fix an integer depth d<=L.  On

    S={x_0,...,x_(L-d)},

the map T^d is injective: an equality T^d(x_i)=T^d(x_j) is the equality
x_(i+d)=x_(j+d), with both indices still within the nonrepeating segment.
It therefore forces i=j.  Crucially, we assert injectivity ONLY at depth d,
not at all future depths.

Inspecting the proof of OrbitPacking.block_card_le shows that at a fixed
block depth d it uses only Set.InjOn (T^d) S.  Its universal hypothesis
IterateSeparated S can be weakened to this single-depth hypothesis.  All
other ingredients, the affine block identity, endpoint bound, and weighted
count, are unconditional.  Hence for every q>=0,

    #{i<=L-d : q 2^d <= x_i < (q+1)2^d} <= B(d),
    B(d)=(d+1)3^floor(3d/5)+floor(3^d/2^(floor(3d/5)+1)).       (1)

This is also a visit-count bound when other states leave the block; the
whole segment need not remain there.  The L-d+1 source states are distinct,
so counting values and counting the specified indices agree.

In particular, if every x_i<2^d, then

    L+1 <= d+B(d).                                           (2)

For d<=L apply (1) to q=0; if L<d, (2) holds trivially.  The final d
indices are the essential headroom cost.  Dropping them prevents the
invalid inference that a finite nonrepeating set is IterateSeparated at
every depth.  No infinite divergent orbit is assumed.

## 2. A power saving in finite residence time

Take d=5t.  Dividing B(5t) by 32^t and relaxing its integer division gives

    B(5t)/32^t <= (5t+1)(27/32)^t + (1/2)(243/256)^t.        (3)

Both ratios are below one.  If every x_i<=X, choose t minimal with
32^t>X.  For X>=1 this gives 32^t<=32X.  Equations (2)-(3) imply

    L+1 = O((1+log X) X^beta + log X),
    beta=log_32(243/8)<1.                                   (4)

The smaller base 27 contributes no larger order.  Constants are absolute.
In particular, the number of consecutive distinct states in [1,X] is o(X).
This is stronger than unordered integer spacing, which permits X such states.
It is an upper bound on an actual contiguous trajectory, not on arbitrary
sets of distinct integers.  Composition of T is the extra information.

## 3. The Christoffel real trajectory has only linear height

Suppose n realizes v_K, and let k_t count odd letters before time t.
The exact affine formula is

    x_t=b_t(n+S_t),
    b_t=3^k_t/2^t,
    S_t=sum_{i<k_t} 2^p_i/3^(i+1).                          (5)

Each summand in S_t is at most 1/3, so 0<=S_t<=K/3.  Also b_t<=3:
if k_t=0, this is immediate; otherwise t>=p_(k_t-1)+1 and

    b_t <= 3^k_t / 2^(p_(k_t-1)+1) < 3.

The strict last inequality follows from 3^(k_t-1)<2^(p_(k_t-1)+1).
Consequently every state, including the endpoint, satisfies

    x_t <= 3n+K.                                           (6)

This bound holds even for the artificial rational trajectory obtained by
following the word without checking parities.  Integrality is used in the
finite packing step, not smuggled into (5)-(6).

To match the earlier spacing hypothesis exactly, it suffices that the K
ODD states are distinct.  Set L=p_(K-1), the time of the last odd letter.
Then x_0,...,x_L are all distinct: if x_i=x_j with i<j<=L, take the
first odd time j+h>=j (which exists by time L).  Determinism gives
x_(i+h)=x_(j+h), a repeated odd value at two indices <=L, a contradiction.
This argument does not assume anything about repeats after the last odd time.

If n<=C K, put X=(3C+1)K, or take its integer ceiling.  This truncated
segment has L+1>=K states, all bounded by X.  Equation (4) would
give K=O(K^beta log K)=o(K), a contradiction for large K.  This proves the
result for every fixed C.  Equivalently, among nonrepeating realizations
with K tending to infinity, n/K must tend to infinity.

## 4. One completely explicit cutoff for C=12

For all integers t>=256,

    ((5t)+B(5t))/32^t < 1/1184.                            (7)

Here is an elementary check, avoiding approximate logarithms.  At t=256:

- (27/32)^5<1/2 by 2*27^5<32^5.  Thus
  (5t+1)(27/32)^t < 1281/2^51 < 1/8192.
- Bernoulli gives (256/243)^19 >= 1+19*13/243 > 2.
  Since 256>=19*13, (243/256)^256 < 1/8192, so its
  half-weighted contribution is <1/16384.
- 5t/32^t=1280/2^1280<1/8192.

Their sum is <5/16384<1/1184.  Each term decreases for t>=256:
for the first, 27(5t+6)<=32(5t+1) holds for t>=6; the second is
geometric; for the third, (t+1)<=32t holds for t>=1.  This proves (7).

Now assume K>=2^1280, n<=12K, and choose t minimal with 32^t>37K.
Then t>=256 and 32^t<=1184K.  If the realizing segment's odd states were
distinct, truncate at L=p_(K-1) as above.  Equations (2), (6), and (7) give

    K <= L+1 <= 5t+B(5t) < 32^t/1184 <= K,

a contradiction.  The cutoff is only an existence certificate; reducing
it is not the research objective, and no finite check below it is claimed.

## 5. Comparison with the previous obstruction and controls

RESEARCH-2026-09-22-astra-integer-spacing.md constructs arbitrarily large
K and many n in [10K,12K] that pass exact j-prefix admission and optimal
unordered distinct-tail spacing when 2^j j^2=o(K).  The argument here
rules out a full NONREPEATING trajectory for every candidate once K is
large enough.  It needs no near-resonance hypothesis on 2^m/3^K.

This is not a second endpoint congruence, a residue-distribution assumption,
or a claim that a short prefix implies full admission.  It uses injectivity
of simultaneous shifted portions of the proposed full trajectory.  The
shifts only have logarithmic length, but are imposed across the long
segment, not merely on its initial logarithmic prefix.

- Repeated states: injectivity fails, as it must.  Actual realizations in
  the stated range would eventually cycle.  First coefficient crossing
  alone does not guarantee distinctness.  Do not claim full rejection.
- 5n+1: the same weight-2 calculation would have good ratio 5^3/32>1
  and bad ratio 3^5/2^8<1; there is no resulting power saving.  In general
  this method needs a threshold above log_2(3/2) and below log_5 2,
  which is impossible.  The multiplier control is not accidentally excluded.
- Rational word trajectories can occupy the linear-height interval with
  distinct rational states.  Integer block cardinality and modular parity
  counting are unavailable, so they do not contradict the theorem.

## 6. What this does and does not open

The targeted admission test succeeds: a trajectory-sensitive inequality
rejects the nonrepeating branch of the exact adversarial family that
defeated scalar spacing.  This is a concrete bounded formalization target:
first expose the existing packing proof with a single-depth injectivity
hypothesis, then prove (1)-(2) for finite nonrepeating traces.  The family
application remains a paper corollary until its positions are formalized.
No treadmill was launched for it during this pass.

For arbitrary first-crossing words there is no bound like (6) in terms of
n+K alone: the intermediate homogeneous coefficients may be very large.
The general first-crossing problem and the repeated-state/cycle branch
remain open.  This is not a uniform CST proof or a proof of nondivergence.
