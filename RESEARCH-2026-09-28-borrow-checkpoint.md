# Borrowing for the lower five-head family

```sh
./experiments/catalytic_palette.py borrow 23273 --max-source-label 30000
./experiments/catalytic_palette.py test
./experiments/borrowability_descent.py test
```

The lower family from [FiveHead.lean](CollatzMoonshot/Obstructions/FiveHead.lean)
has `n=9223+16320h`, `c=3689+6528h`, `d=5425+9600h`, and the legal exchange
`{5n,c}->{n,d}`, with both `c,d<n`.  This pass supplies four exact borrowing
instances without using the trajectory of n, and a general Lean obstruction
to supplying unbounded labels with bounded-size unit words.

## Borrowing instances, including the first longer-growth control

| h | n | Borrowed c | Total factors in final unit | Largest final label | Largest construction label |
|---:|---:|---:|---:|---:|---:|
| 0 | 9223 | 3689 | 292 | 128401 | 128401 |
| 1 | 25543 | 10217 | 61 | 10217 | 128401 |
| 2 | 41863 | 16745 | 357 | 18785 | 18785 |
| 3 | 58183 | 23273 | 643 | 7062293 | 7062293 |

Every word is constructed from U2/U8/U13 and legal quadratic exchanges,
using a validated saved borrowing DAG as its initial library.  The new
`borrow` command accepts only the target auxiliary label; it does not
consult `wild_five_repair` or a known orbit.  The final word is a positive
unit containing that auxiliary.  Construction height records all used
intermediate labels, including labels consumed before the final word.
These are witness costs, not proved minima.

The last new edges are

```
{2635,3953} -> {2767,3689},
{5035,128401} -> {9215,10217},
{785,3349} -> {661,16745},
{1369,2327} -> {895,23273}.
```

For the fourth case the borrowing of 2327 uses
`{3043,9877}->{2327,7062293}`.  The large companion remains in the final
unit.  The first three searches cap source labels at 20000; the fourth at
30000.  All cap complete neighbor calls at 20, recursion depth at 2,
candidate branches at 80 per query, and final unit factors at 100000.
The successful first/fourth searches still record candidate-branch
truncation.  They provide positive witnesses, not completeness results.
The saved files are `experiments/borrow_{3689,10217,16745,23273}.json`.

## The family contains arbitrarily long growth

Writing `n=64k+7` gives `k=144+255h` and
`T^6(n)+1=11675+20655h`.  For every j, the coefficient 20655 is invertible
modulo `2^j`, so a residue class of h supplies j further odd steps, all
strictly increasing.  Thus the family has no uniform bound on time to
first descent.

However h even descends at step 7, and h=1 mod4 at step 8.  Our original
three tests h=0,1,2 all fall in these easy slices; h=3 is the first remaining
slice.  There `T^6(n)=73639` and `73640=8*9205`, giving three further odd
steps before the odd run ends.  No target orbit is used by its borrowing
search.  The [symbolic audit](RESEARCH-2026-09-28-lower-five-head-audit.md)
proves the domain statements on paper and computes the eight distinct
vertex charges changed by the Q move.  Installing the genuine first edge
from n does not establish a decrease in the full certificate defect.

## Bounded unit size forces bounded support

[UnitSupportBound.lean](CollatzMoonshot/Obstructions/UnitSupportBound.lean)
now proves a stronger arithmetic statement: if a list of positive integers
satisfies

```
a * product(u) = b * product(3u+1),   0<b<=B,
```

then every label is bounded by `productLabelBound(length,B)`, independently
of a.  For an exact unit `2^t product(2u/(3u+1))=1`, take
`a=2^(t+length)` and `b=B=1`.  Consequently bounded odd-factor count gives
bounded labels.  A bound on count by Q instead of an exact count follows
by taking the maximum of these bounds for q=0,...,Q.

The proof repeatedly removes a least label.  The remaining product
`product(3+1/u)=a/b` exceeds `3^q` by at least `1/b`, because its numerator
gap is a positive integer.  A telescoping upper bound then bounds the
least label and the next denominator.  This is independent of our chosen
palette and does not assume Collatz convergence.

It rules out a fixed-size unit template containing the unbounded
`c(h)=3689+6528h`.  It permits a recursive construction whose word size
grows with h.  Optimizing the coarse numerical bound is not a prerequisite
for finding that construction.

## Another candidate recursion tested and narrowed

For `u_j=(4^j-1)/3`, the natural complementary split into `u_i` and
`u_(j-i)` forces companion `u_i*u_(j-i)/(u_i+u_(j-i))`, which has an even
denominator and is never integral.  This is an infinite obstruction to that
particular split, proved on paper.  The whole dyadic family is not an
obstruction to two-smaller-input introduction: the exact rule
`{5461,7453}<->{3683,21845}` is a counterexample.  The
[dyadic height study](RESEARCH-2026-09-28-borrow-height-structural.md)
records the valuation sieve and bounded controls.

A proposed composition with the old connected-pair identity also fails
exactly at parity: writing `c=17s,d=25s,n=(85s+1)/2`, its two companion
labels are even precisely when n is odd.  Replacing those formal factors
by actual even edges breaks the identity.  The symbolic audit records
the incompatibility; it does not exclude a longer repair with new factors.

## Remaining research and validation

The next mathematical object is a recursively specified borrowing scheme
with an exact parameter domain and a decreasing recursion measure, allowing
word size and intermediate labels to grow.  That would address availability;
completion of the resulting virtual word without a supplied target path
would still be separate.  None of the four finite DAGs yet provides such a
recurrence.  The other two original research branches retain their separate
missing inequalities.

The two unit-support statements are proved with their frozen definitions
and types unchanged.  The bounded Opus/low task completed in one lap; the
supervisor verified the full build on the host.  The installed real-CLI
regression suites pass 28 tests.  Tests reconstruct borrowing words in DAG
order, check exact rational identities and factor availability, distinguish
final from construction height, and retain the old repair regressions.
