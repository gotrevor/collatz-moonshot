# Catalytic certificate repair and the exact anchored operator constant

```sh
./experiments/research_lifts.py test
./experiments/research_lifts.py controls --structural
./experiments/research_lifts.py quadratic-neighbors 7
./experiments/research_lifts.py unit-assisted-seven
./experiments/research_lifts.py palette-obstruction
```

This continues the [three-direction follow-up](RESEARCH-2026-09-27-arithmetic-lifts-followup.md).  The main advance is a concrete repair of its atomic defect using borrowed unit factors.  The repair reveals two different kinds of obstruction: some cubic exchanges become quadratic after adding a catalyst, while others remain impossible with every catalyst.  The pairwise direction loses a proposed dyadic input to an exact coding identity.  The operator direction now has an exact, nonuniform constant, identifying precisely the dynamical estimate it would need.

Throughout, T is the shortcut Collatz map, and `r_u=2u/(3u+1)` for positive odd u.  These are statements about certificate transformations and operator estimates, not a convergence proof.  No literature-priority claim is made for the identities derived here.

## 1. A repair that actually leaves the four-charge local minimum

The previous certificate `2^4 r_35 r_53=7` was not a path.  Its defect with the specified even background was `e_16+e_35-e_80-e_7`.  Introduce two positive words of value one:

```
U8  = 2^3 r_19 r_25 r_29 r_55 r_83,
U13 = 2^5 r_5 r_7^2 r_11 r_17 r_55 r_65 r_83.
```

For U8, cancellation reduces the odd product to `(19/38)(25/125)(55/44)=1/8`.  U13 is the [Applegate-Lagarias inverse-5 certificate](https://arxiv.org/html/math/0411140), multiplied by the four-step certificate for `5 -> 8 -> 4 -> 2 -> 1`.

Multiply the stalled certificate by U13.  Then perform these eight replacements, each involving two available odd factors and preserving their product:

| Remove | Insert |
|---|---|
| 35, 53 | 25, 133 |
| 65, 133 | 53, 247 |
| 17, 53 | 13, 901 |
| 247, 901 | 221, 1577 |
| 11, 221 | 13, 55 |
| 55, 1577 | 95, 121 |
| 13, 95 | 19, 29 |
| 7, 121 | 11, 17 |

The result is

```
(2^6 r_7 r_11 r_17 r_13 r_5) * U8.
```

Remove U8.  The remaining factors are the actual 11-step path from 7 to 1.  Every intermediate scalar value is 7, and no factor multiplicity becomes negative.  Intermediate labels grow as high as 1577; monotonicity in height is not claimed.

`CatalyticRepair.lean` checks the unit values, availability and scalar equality of every replacement, and the endpoint multiset.  This is a concrete repair of the previously stalled example, not yet a terminating rule for an arbitrary certificate.  The construction used the known target path for 7; it does not independently discover a path for an unknown start.

### A cubic exchange which becomes quadratic only after adjoining a factor

At the center is the identity

```
r_7 r_65 r_133 = r_13 r_19 r_29 = 247/880.
```

Without extra factors, the entire quadratic component on the left consists of exactly two multisets:

```
{7,65,133}, {7,53,247}.
```

This is not a search cutoff.  The high pair satisfies

```
(17c-741)(17d-741)=553280.
```

For positive odd `c<=d`, the smaller label is below 88, and the only solutions are `(53,247)` and `(65,133)`.  Every pair involving 7 in these two states has no nontrivial replacement.  Lean proves both the unbounded pair classification and the induction over arbitrarily many replacements: `cubic_exchange_not_quadratic`.

With the extra factor r_121, however, there is a path:

```
7,65,121,133
11,17,65,133
11,17,53,247
11,13,247,901
11,13,221,1577
13,13,55,1577
13,13,95,121
13,19,29,121
```

The catalyst is returned at the end.  `explicit_quadratic_catalyst` checks this path.  Thus cancellation of a common factor is not valid for reachability under the quadratic rules, even though it is valid for equality of rational products.  This distinction is useful: the right object for local repair includes available auxiliary factors, not just the reduced scalar identity.

### The quadratic interaction list of a fixed generator is finite and computable

There is a complete way to find every nontrivial quadratic exchange involving a fixed r_a, with no partner-height bound.  Write a replacement as

```
r_a r_b = r_c r_d,   c<=d.
```

Since `r_c^2 <= r_a r_b < (2/3)r_a` and `r_(2a+1)^2 > (2/3)r_a`, we have `c<2a+1`.  Equivalently, the integral pair equation is

```
(3(a+b)+1) c d = ab(3(c+d)+1).
```

For `c!=a`, put

```
alpha=3(a-c), beta=a(3c+1), gamma=c(3a+1).
```

Then `alpha*b*d+beta*b-gamma*d=0`.  If alpha is positive, `b<gamma/alpha`; if alpha is negative, `d<beta/(-alpha)`.  Enumerate that bounded variable and solve for the other.  The case c=a is the unchanged pair.  This proves completeness of `quadratic-neighbors` without assuming a bound on b or d.

For a=7 the complete list is

```
{7,121} <-> {11,17},
{7,261} <-> {9,29},
{7,429} <-> {13,15}.
```

In a certificate of a 3-free rational, every odd label is 3-free: T(u) is never divisible by 3 for odd u, so no denominator cancels a numerator's 3-adic charge.  Consequently 121 is the **only** possible partner that can move a 7 in this setting.  The successful catalyst is therefore explained by the complete interaction list, not just by a lucky search.

### Some cubic rules are essential even with arbitrary catalysts

The generators r_1, r_3 and r_5 are frozen under quadratic substitutions.  For a=5, the smaller replacement c can only be 1,3,5,7,9.  The preceding equation gives these finite cases:

* c=1 forces b<2;
* c=3 forces b<8;
* c=5 forces d=b;
* c=7 forces d<19;
* c=9 forces d<12.

Positivity, oddness and the linear equation leave only the unchanged pair.  The cases a=1,3 are shorter.  Reversing the equality shows these factors cannot be created either.  Their multiplicities are invariants of any sequence of quadratic exchanges, with arbitrary finite context.

But

```
r_5 r_55 r_83 = r_11 r_13 r_17 = 11/40.
```

The left has one r_5 and the right has none.  No catalyst can make this exchange quadratic, because the identical catalyst contributes the same r_5 count to both sides.  `QuadraticInvariants.lean` is the separately assigned formalization of this universal statement; its final status is recorded below.

The complete neighbor probe through a=101 found only 1,3,5 frozen.  Each individual list is complete over all partner heights; the assertion that there are no other frozen labels beyond 101 is **not** established.

### The first fixed unit palette has an invariant, and the new cubic breaks it

Allow arbitrary quadratic replacements and insertion/removal of `2r_1`, U8 and U13.  For t factors of 2, k odd factors, and multiplicities m_1,m_5, define

```
I = 5t - 3k - m_5 - 2m_1.
```

Quadratic moves preserve it by the frozen-factor result; each of the three unit words has I=0.  The published 32-factor certificate for 71 has I=31.  The actual 65-step certificate has 28 even and 37 odd steps, includes one r_5 and no r_1, so I=28.  Extra turns around `1 -> 2 -> 1` add `2r_1` and cannot change I.  Thus this fixed palette, despite repairing 7, **cannot repair that certificate for 71 into any path to 1**.

The essential cubic above changes I by one.  Applied to U13 it produces a new unit, of value one but I=1:

```
U13' = 2^5 r_7^2 r_11^2 r_13 r_17^2 r_65.
```

This supplies an explicit next rule, selected by an invariant that actually obstructed the next control.  It does not establish that the enlarged palette repairs 71 or is complete in general.

The count vectors of U8 and U13, `(3,5)` and `(5,8)`, have determinant -1.  Thus counts of twos and odd factors alone supply no remaining additive invariant after allowing these units.  The failure at 71 demonstrates why multiplicities of specific generators must also be retained.

### Minimal unit sizes

Remove all copies of `2r_1` from a nontrivial unit word.  There are then no r_1 factors: if the twos ran out first, the remaining product of odd generators would be strictly below one.  There are no 3-divisible labels either.  All remaining labels are at least 5, so

```
2^t (5/8)^k <= 1 < 2^t (2/3)^k.
```

Below total length 8, the only possible counts are `(t,k)=(2,3)`.  The same is true below **odd** total length 13.  A product of three odd generators equal to 1/4 would have least label 5, since `(7/11)^3>1/4`.  The other pair would have product 2/5, forcing `(c-3)(d-3)=10`, impossible for odd c,d modulo 4.  Thus U8 is a shortest nontrivial reduced unit, and U13 is a shortest odd-length unit.  Lean currently checks the odd-length count reduction and the explicit units; the full normalization/minimality argument here remains paper-side.

**Research direction now:** catalytic rewriting with a small, explicitly justified rule palette.  Use exact interaction lists to choose useful borrowed factors, and conserved multiplicities to detect missing rule families.  A blanket permission to insert *every* value-one word would lose the content: on the 3-free part, the semigroup theorem already supplies inverse certificates, making unrestricted unit-assisted equivalence tautological.  The unresolved task is a controlled repair procedure and a termination argument that produces actual vertex balance.

## 2. The dyadic Vandermonde ledger contains exactly prefix-collision data

For a primitive rational shortcut cycle `x_0,...,x_(m-1)` with odd denominators and parity word w, let l(i,j) be the number of initial matching symbols in the two periodic rotations beginning at i,j.  Then

```
v_2(x_i-x_j) = l(i,j).
```

Proof: while the current parities agree, their difference is multiplied by either 1/2 or 3/2, lowering its 2-adic valuation by exactly one.  At the first different parity, the difference is odd.  Primitive rotations disagree before length m; reversing these steps proves the formula.  This is the classical parity-coding isometry, here applied to the pair product.

Let C_q(v) count rotations beginning with a specified binary q-word v.  Double-counting matching prefixes gives

```
v_2(Vandermonde(x)) = sum_(q>=1) sum_(v in {0,1}^q) binom(C_q(v),2).
```

For `11111000` the successive contributions are 13,7,3,1, totaling 24.  Its rational cycle has denominator 13 and minimum real gap 69/13, yet satisfies the formula exactly.  The whole dyadic pair ledger is therefore already fixed by symbolic prefix collisions; it supplies no further integer-admission test.  This retires one candidate source of new arithmetic in the pairwise direction.  A useful remaining inequality would have to combine closure with information beyond this ledger, for example genuine odd-prime denominator restrictions and real ordering.  No such excluding inequality is claimed here.  The general coding argument is paper-side, with exact rational CLI controls.

## 3. The sharp anchored defect bound is exactly an orbit-height quantity

Fix `n>=3`.  On nonnegative real coefficient sequences with finite norm

```
||a|| = sum_(u>=1) a_u/u,
```

require `a_1=a_2=0` and `a_n=1`.  Let P be the actual transfer operator from the earlier note, and define

```
c_n = inf ||(P-I)a||
```

over this class.  This is a bound relative to the **anchored coefficient**, not the previous bound relative to `||a||`.  P is bounded by 2 in this norm.

**Sharp result.**  If n has a bounded, nonperiodic forward orbit and
`M_n=max_{j>=1} T^j(n)`, then `c_n=1/M_n`.  If its orbit is unbounded, `c_n=0`.  If n is on a nontrivial cycle, `c_n=0`.  The same infimum is obtained even when restricting to connected 0/1 support of size `O(log X)` below X for each individual candidate.

**Lower bound for a bounded, nonperiodic start.**  Let A be its finite strict future set.  It contains T(n), is forward closed, and excludes n.  Write `b=(P-I)a`.  Finite flow cancellation gives

```
sum_(v in A) b_v = sum_(u outside A, T(u) in A) a_u >= a_n = 1.
```

There are finitely many incoming vertices because T has at most two positive preimages.  Hence

```
1 <= sum_(v in A) |b_v| <= M_n * sum_(v>=1) |b_v|/v.
```

This is an actual dual certificate, with no assumption on how mass splits among the other preimages.

**Attaining the bound.**  Let q=M_n be its first occurrence at time L.  For any positive n, including even n,

```
D_n = sum_(h>=0) z^(2^h n),       (P-I)D_n=z^T(n).
```

Set

```
F = D_n + sum_(j=1)^(L-1) z^T^j(n).
```

The finite sum telescopes, so `(P-I)F=z^q`.  The prefix is distinct and disjoint from the ray: a forward visit to `2^h n` would return to n after h halvings, contradicting nonperiodicity.  Thus F is 0/1, has anchored coefficient one, and has connected support.  It avoids 1,2 up to the chosen endpoint and has weighted defect exactly 1/q.  Its support is a dyadic ray plus a finite set.

For an unbounded orbit, the same construction at arbitrarily large endpoints gives defect norms tending to zero.  For a nontrivial cycle, its indicator is an admissible exact fixed vector.  These prove the remaining cases.

Hand controls: n=3 gives `D_3+z^5`, defect at 8, `c_3=1/8`; n=7 gives `D_7+z^11+z^17`, defect at 26, `c_7=1/26`; n=8 gives `D_8`, defect at 4, `c_8=1/4`.

Consequently `c_n>0 for every n>=3` is equivalent to Collatz convergence.  If all constants are positive, there are no unbounded orbits and no nontrivial periodic states.  Conversely, convergence gives the finite-cut lower bound for each n.  The identity locates the analytic target exactly: a nonuniform anchored estimate is a peak-height bound, together with exclusion of periodic states.  Changing the exponent of the power weight only changes the power of the same orbit-height quantity.  The same proof gives `M_n^(-s)` for weights `u^(-s)`, s>0.

This sharp anchored result is a paper proof with exact extremizer controls; its general finite-cut identity and infimum statement have not yet been formalized in Lean.  Separately, the previously open `PositiveApproximationFamily` has now been proved in `PositiveApproximation.lean`, without changing its statement.  Its norm and sparsity consequences remain as recorded in the prior note.

## Evidence and next crux

The persistent suite has 38 CLI tests.  `experiments/catalytic_repair_controls.json` records the small complete components, the successful catalyst path, the full eight-move repair, frozen-generator lists, the palette obstruction, and the operator extremizers.  A path found in a bounded graph is an exact witness.  Failure is called a complete-component obstruction only when the queue is exhausted and no height pruning occurred.

Lean files: `MinimalRepairs.lean` proves the unbounded two-state obstruction; `CatalyticRepair.lean` checks the explicit positive repair witnesses; `PositiveApproximation.lean` proves the general coefficient family.  `QuadraticInvariants.lean` is assigned the all-catalysts obstruction.  The mathematical crux is still a terminating repair mechanism with actual vertex balance.  The new local machinery does not supply that theorem.
