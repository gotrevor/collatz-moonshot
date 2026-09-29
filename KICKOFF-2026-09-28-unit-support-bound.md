# Bounded proof task: bounded unit size forces bounded label support

Own only `CollatzMoonshot/Obstructions/UnitSupportBound.lean` and
`HANDOFF-2026-09-28-unit-support-bound.md`.  Other agents own experiments and
notes.  Frozen definitions and the two statement types must remain unchanged.
No broad Collatz campaign; this is a proved elementary obstruction assigned by
the attended operator under Trevor's continuing research mandate.

## Exact paper proof

Prove the stronger rational-product theorem by induction on list length, with
all other parameters generalized.  An empty list is vacuous.  In the nonempty
case choose a least label v, erase one occurrence, and put q=xs.length>0.
All labels are positive, hence at least 1 and at least v.

The cross identity implies

```
 a/b = product (3 + 1/u) > 3^q.
```

Consequently the natural integer a-3^q*b is at least 1, so
`a/b - 3^q >= 1/b >= 1/B`.

For labels u>=v>=1, each 3+1/u is at most 4.  Telescoping the product gives

```
product (3+1/u) - 3^q <= q * 4^(q-1) / v <= q*4^q/v.
```

Thus `v <= q*4^q*B = m`.  Removing v leaves exactly the cross identity with
`a'=a*v` and `b'=b*(3*v+1)`, and
`0<b'<=B*(3*m+1)`.  Apply the induction hypothesis to the remaining list,
then combine its bound with v<=m using the `max` in productLabelBound.

One useful analytic helper can be proved by list induction over positive
rational x_i=1/u_i with 0<x_i<=1 and x_i<=1/v:
the product of (3+x_i) is strictly >3^length, while its excess is at most
length*4^length/v.  The loose 4^length avoids predecessor arithmetic.
Alternatively prove the telescoping estimate directly after clearing natural
denominators; choose the easiest implementation.  Sorting is unnecessary if a
minimum member and `List.erase` plus product-permutation lemmas are easier.

The unit theorem follows by b=B=1.  No Collatz trajectory assumptions, no
oddness, and no axiom are needed.  This is about exact positive units, not a
bound on full Collatz certificates.  The coarseness of the recursive bound is
intentional; do not optimize it.

Build the new module then root.  Quietly audit both frozen declarations,
commit green and stop.  A handoff should explain that unbounded auxiliary
labels require unbounded unit size; it should not redirect the next research
step into routine list plumbing.
