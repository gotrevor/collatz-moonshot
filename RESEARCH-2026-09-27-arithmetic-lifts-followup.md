# Three arithmetic lifts: a local repair, a local minimum, and a cone obstruction

Run the persistent suite and reproduce the principal controls:

```sh
./experiments/research_lifts.py test
./experiments/research_lifts.py two-edge-repair --parameter 1
./experiments/research_lifts.py two-odd-fiber --ratio 7/16
./experiments/research_lifts.py wild-five-repair 71
./experiments/research_lifts.py gap-control --parameter 1
./experiments/research_lifts.py controls --followup
```

This follows [the three proposals](RESEARCH-2026-09-27-three-arithmetic-lifts.md).  All maps below use the shortcut convention `T(n)=n/2` for even n and `(3n+1)/2` for odd n.  A local repair mechanism was found in direction 1, together with an exact obstruction to making that mechanism a complete monotone algorithm.  Direction 2's first arithmetic simplifications add no exclusion.  Direction 3 now has an explicit quantitative obstruction on the actual Collatz operator, stronger than the previous different-map control.

## 1. A genuine parametric neutral exchange

Put `r_u=u/T(u)` for positive odd u.  For every positive `t=1 mod4`,

```
r_(23t) r_((483t+7)/2) = r_(35t) r_((105t+1)/2).
```

All four labels are positive odd integers.  The two factors on the right are the actual consecutive edges

```
35t -> (105t+1)/2 -> (315t+5)/4.
```

The left edges are disconnected.  Their boundary is

```
e_(23t) - e_((69t+1)/2) + e_((483t+7)/2) - e_((1449t+23)/4),
```

whose four labels are distinct.  The right boundary is

```
e_(35t) - e_((315t+5)/4).
```

Thus the boundary's integer l1 norm decreases from 4 to 2.  This gives a precise domain on which the *whole certificate defect* decreases: if the background defect vanishes on the union of these boundary supports, the exchange decreases its l1 norm by exactly 2.  No unconditional claim is made when background charges overlap those labels.

The identity was obtained algebraically, not by enumerating convergent orbits.  More generally, for odd k,t with `kt=3 mod4`, the connected pair beginning at `5kt` has the neutral alternative

```
r_(5kt) r_((15kt+1)/2)
    = r_((3k+2)t) r_(k*((9k+6)t+1)/2).
```

The displayed family is k=7.  Cross multiplication proves the identity; the congruence checks that its labels are genuine odd-edge generators.  At t=1 it says `r_23 r_245 = r_35 r_53 = 7/16`; at t=5 it says `r_115 r_1211 = r_175 r_263 = 35/79`.

### The complete two-factor fiber has a nonzero local minimum

Attach the background even path `16 -> 8 -> 4 -> 2 -> 1`.  Both

```
2^4 r_23 r_245 = 7,
2^4 r_35 r_53 = 7
```

are valid semigroup certificates.  Their vertex defects relative to `e_7-e_1` have l1 norms 6 and 4 respectively.  After the repair the defect is

```
e_16 + e_35 - e_80 - e_7.
```

Neither certificate is an actual path to 7.  This is not merely a failure to discover another pair substitution: **all** positive odd pairs c,d with `r_c r_d=7/16` can be classified exactly.  Cross multiplication gives

```
(c-21)(d-21)=448.
```

Both factors must be positive: from the uncompleted-square equation,
`d(c-21)=21c+7>0`.  Both are even.  Factoring 448 therefore gives exactly the five unordered pairs:

| Odd sources | Defect l1 with the fixed even background | Actual path? |
|---|---:|---|
| 23,245 | 6 | No |
| 25,133 | 6 | No |
| 29,77 | 6 | No |
| 35,53 | 4 | No |
| 37,49 | 6 | No |

Consequently the repaired certificate is a strict local minimum over the **entire two-odd-factor fiber**, not just over the single parametric rule.  The even background is fixed in this assertion.  Independently of how one orders the scalar factors, the shortest actual path from 7 to 1 has 11 edges, while these certificates have only 6 factors.

The probe's general exact fiber algorithm uses, for `r_c r_d=A/B` in lowest terms and `D=4B-9A>0`,

```
(Dc-3A)(Dd-3A)=4AB.
```

Both factors are positive; enumerating divisors of `4AB` has no generator-height cutoff.

### Why l1 descent reaches the hard part immediately

Every certificate defect d has total coordinate sum zero and `Ld=0`, where L records prime valuations.  A nonzero such integer vector has l1 norm at least 4.  Indeed norm 2 would force `d=e_a-e_b`; equality of all prime valuations gives a=b, so d=0.  The displayed four-charge defect already attains this minimum.

A strictly l1-decreasing repair of a norm-4 defect must therefore remove the *entire* defect in one exchange.  The local rule can simplify a larger defect, but the norm supplies no intermediate descent inside an atomic multiplicative relation.  Such relations have the form

```
e_(gx) + e_(hy) - e_(gy) - e_(hx).
```

For this example `(g,h,x,y)=(16,7,1,5)`.  This identifies a concrete next object: transformations of these four-charge multiplicative relations that permit factor growth and use a finer measure than l1.  No terminating rule for them is known here.

### Factor count fails on the published constructive input too

The [Applegate-Lagarias construction](https://arxiv.org/html/math/0411140), Table 3, supplies

```
1/5 = 2^2 r_7^2 r_11 r_17 r_55 r_65 r_83.
```

For `n=7 mod64`, the genuine six-step trajectory from `5n` ends at `(45n+5)/64<n`.  These two facts give a concrete family of semigroup certificates, after attaching a certificate for the smaller endpoint.  This uses their construction, not an assumed Collatz proof.

At n=71 the smaller endpoint is 50.  Its actual path has 17 edges; the virtual prefix contributes 6 and the inverse-5 certificate contributes 9, for **32 factors total**.  The actual shortest path from 71 to 1 has **65** edges.  Already its 32nd iterate is 1619, which excludes reaching the invariant `{1,2}` cycle within 32 steps.  The original certificate's odd labels are

```
25,19,29,11,17,13,5,355,533,7,7,11,17,55,65,83,
```

with 16 factors of 2.  A repair cannot always decrease total factor count.  The largest odd label also has to grow in this example, from 533 to 3077 along the actual path.

There is a second general constraint on a bounded repair of this virtual descent.  If words of lengths a,b make n and `m=(45n+5)/64` meet, write their numerators A,B and odd counts k,l.  Then

```
(64*2^b*3^k - 45*2^a*3^l)*n
    = 5*2^a*3^l + 64*2^a*B - 64*2^b*A.
```

The coefficient of n is nonzero modulo 5.  Since `0<=A<3^a`, `0<=B<3^b`, and `k<=a`, `l<=b`, putting `L=max(a,b)` gives `n<69*6^L`.  Thus no uniform bounded meeting length can repair this entire progression.  Adaptive or growing-length transformations remain possible; this is a lower bound on what they must do, not a refutation of all semigroup lifts.

## 2. What the pairwise arithmetic does and does not add

The exact Vandermonde transport identity from the first note remains valid.  Its first proposed arithmetic strengthening needs a sharp distinction between the *individual differences* and their product.

**Proposition.**  If a rational set S contains x and x/2, all pairwise differences in S are integers if and only if all its points are integers.

Proof: `x-x/2=x/2` is an integer, hence x is an integer.  Subtract x from every other point.  The reverse implication is immediate.  Every positive rational Collatz cycle has an even edge: if all steps were odd, `(3x+1)/2>x` would strictly increase at every step.  Therefore the proposition applies to the intended cycle population.  Requiring integral gaps simply reintroduces state admission.

The weaker requirement that the Vandermonde product be integral is insufficient for sets even when they have an actual halving edge and large real gaps.  For every positive integer t, take

```
S_t = {63/5, 126/5, (126+125t)/5}.
```

It has the edge `126/5 -> 63/5`, minimum gap `63/5>1`, and integer absolute Vandermonde

```
V(S_t)=63*t*(63+125t).
```

All its states are nonintegral.  The sets are **not closed cycles**: for example `T(63/5)=97/5` is absent.  Thus this only refutes dropping full cycle closure while replacing individual gap information by the product.  It does not refute a stronger cycle-specific inequality.

The persistent scan also examined 7,551 positive primitive rational cycles up to length 16, one representative per rotation.  It found no nonintegral cycle with an integral discriminant.  This finite observation is not a theorem, and proving that equivalence would not yet exclude an integer cycle.  The next useful claim must be a strict inequality from *joint order, residue clustering, and closure*, with exclusion strength beyond the existing admission condition.  No such inequality emerged in this pass.

## 3. The actual positive cone has no uniform coercivity bound

Let `P(z^n)=z^T(n)` and `D_a(z)=sum_{h>=0} z^(2^h*a)`.  Work first in the weighted coefficient norm

```
||F||_s = sum_{n>=1} |a_n| n^(-s),  s>0.
```

P is bounded here: `T(n)>=n/2` gives `||P F||_s<=2^s||F||_s`.  For K>=2, put

```
n_j = 3^j*2^(K-j)-1,  0<=j<=K,
F_K = D_(n_0) + sum_{j=1}^{K-1} z^(n_j).
```

For j<K, n_j is odd and `T(n_j)=n_(j+1)`.  The finite forward points are odd and strictly increasing, while the dyadic ray has only one odd point, n_0.  Thus F_K has coefficients 0 or 1, connected support, and its least exponent is `n_0=2^K-1`.  The two geometric sequences give a counting bound `O(log X)` with a constant independent of K, stronger than the required sublinear power bound.

For odd a, `P D_a=D_a+z^T(a)`.  The finite forward sum telescopes, giving the exact one-point defect

```
P F_K - F_K = z^(n_K),    n_K=3^K-1.
```

Consequently

```
||P F_K-F_K||_s / ||F_K||_s
    <= ((2^K-1)/(3^K-1))^s
    < (2/3)^(sK).
```

**No positive constant c can make `||(P-I)F||_s >= c||F||_s` hold for all these positive connected sparse integer-coefficient series**, even though they avoid exponents 1 and 2.  This is the exact refuted estimate.  It is not a claim about every possible Banach norm or about a spectral gap stated modulo the entire fixed subspace.

At K=2, `F_2=D_3+z^5`, the error is `z^8`, and for s=1 the relative error is `(1/8)/(2/3+1/5)=15/104`.  At K=3 the corresponding ratio is `1309/14820`.

### Even exact fixed functions can have arbitrarily little negative mass

For any q, `P D_(2q)=D_(2q)+z^q`.  Therefore

```
H_K = F_K - D_(2*n_K)
```

is **exactly fixed**, not approximately fixed.  Restrict to even K.  Then n_0 is divisible by 3 and n_K is not, so their dyadic rays are disjoint; the remaining positive points are odd and the negative ray is even.  The signs are therefore exactly as displayed.  Its negative-to-positive weighted mass ratio satisfies

```
||(H_K)_-||_s / ||(H_K)_+||_s
    < (2/3)^(sK)/(2^s-1).
```

At K=2, `H_2=D_3+z^5-D_16`.  This construction is also the finite telescoping sum of the known signed fixed functions `D_(3u+1)-D_u`, with a minus sign, along the initial odd segment.  The signed fixed-function family is due to the established operator literature, including [Neklyudov](https://arxiv.org/html/2106.11859v4); the point here is the explicit lack of uniform separation from the positive cone.  Related work [Béhani](https://arxiv.org/abs/2303.03203) studies the operator's weighted-space dynamics; no general spectral novelty is claimed.

H_K is not nonnegative.  Its negative ray and positive support meet through a zero-coefficient endpoint, so its induced nonzero support need not be connected.  F_K, the positive approximate vector used in the coercivity obstruction, *is* connected.  These scope distinctions matter.

The original qualitative question about exact nonnegative fixed series is still open.  A method must distinguish exact positivity from exponentially small negative leakage; a uniform norm gap cannot do it.  An estimate anchored at a fixed starting integer is not contradicted by this construction, whose least exponent tends to infinity.  Obtaining such an estimate without importing that integer's eventual convergence remains the missing input.

## Formalization and reproducibility

`CollatzMoonshot/Obstructions/ArithmeticLifts.lean` records:

* the exact 32-factor certificate for 71 and the negation of universal length-nonincreasing repair;
* the local neutral identity (cross-multiplied for all rational t), its actual-edge anchor, and the exact factor equation for the two-factor fiber;
* the general pair-integrality equivalence and the parametric Vandermonde control;
* the general geometric endpoint-ratio bound and the exact finite approximation anchor.

`PositiveApproximationFamily` pins the full general coefficient statement.  It was initially an unproved Prop; the subsequent bounded helper proved `positiveApproximationFamily : PositiveApproximationFamily` in `PositiveApproximation.lean` (commit `70f312e`).  The general coefficient defect identity is now formalized.  Sparsity and norm consequences remain paper-side.  The finite tests evaluate the infinite rays by formula, including preimages outside the requested display cutoff, so they do not introduce a truncation-boundary error.  The 24-test suite uses hand-derived anchors and drives the actual CLI.  The saved depth-8 operator controls evaluate through exponent 14,000, including the defect at 6,560 and the first negative coefficient at 13,120.

Saved outputs: `experiments/arithmetic_lifts_followup.json`.  The two-factor fiber enumeration is exact by divisor classification.  The cycle discriminant scan is only a finite census.  No Collatz convergence or cycle-exclusion theorem is claimed.

**Next research priority:** the atomic four-charge relations in direction 1.  They are a more precise target than an unspecified certificate repair.  Direction 2 still lacks an excluding inequality; direction 3 needs a nonuniform arithmetic argument rather than a uniform cone gap.  No new general Collatz proof campaign is justified by this pass.

**Subsequent advance:** [catalytic repair and the sharp anchored constant](RESEARCH-2026-09-27-catalytic-repair.md) escapes this local minimum and identifies the next exact obstruction.
