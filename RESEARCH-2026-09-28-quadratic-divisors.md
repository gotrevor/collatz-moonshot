# Complete quadratic interaction lists through positive divisors

```sh
./experiments/research_lifts.py quadratic-neighbors 3077
./experiments/research_lifts.py test
```

The complete interaction list for a fixed generator can be computed without the long scan over a potential partner.  This is a change to the existing exact probe, not a height-bounded replacement.

For positive odd a,b,c,d with c<=d, the equality r_a r_b=r_c r_d implies c<2a+1.  This bound was proved in the earlier catalytic note.  For c!=a, put

```
alpha=3(a-c), beta=a(3c+1), gamma=c(3a+1).
```

The integral relation is alpha*b*d+beta*b-gamma*d=0.  Rearrange it as

```
(gamma-alpha*b)(beta+alpha*d)=beta*gamma.
```

Both factors are positive: they equal beta*b/d and gamma*d/b respectively.  Enumerate positive divisors X of beta*gamma, put Y=beta*gamma/X, and recover

```
b=(gamma-X)/alpha, d=(Y-beta)/alpha.
```

Keep exactly the integer positive odd solutions with d>=c.  The case c=a gives only the unchanged pair.  This covers both signs of alpha.  Factoring beta*gamma uses the four small parts a,c,3c+1,3a+1 separately, so the probe never trial-factors their large product.

The existing `quadratic-neighbors` command now uses this method.  Its API and completeness claim are unchanged.  The positive-divisor helper is shared with the existing two-factor fiber enumerator.  Persistent CLI controls check the three frozen generators, the complete small interaction lists for 7 and 9, and both orientations of the identity r23*r245=r35*r53=7/16.

## Targeted borrowing instead of another global height sweep

The previous six-round unit closure missed 911,1367,1619,2429,3077 on the known path for 71.  Their complete interaction lists are saved in `experiments/target_quadratic_neighbors_71.json`; targeted auxiliary probes are in `experiments/target_aux_neighbors_71.json`.  Exact examples:

* {2485,3029} -> {1367,933205} supplies 1367 from two already borrowable factors.
* {671,2033} -> {583,3745}, followed by {2809,3745} -> {1619,185645}, supplies 1619.
* {233,14135} = {257,2123} supplies 14135; the complete 2429 list includes {2429,98099213} = {2933,14135}, with 2933 already borrowable.

These are witnesses of borrowing, not statements that labels missing from the old cutoff were impossible.  Large auxiliary labels are permitted because they are supplied by explicit unit constructions, not by an unrecorded permission to adjoin arbitrary factors.

The integer-lattice worker subsequently needed only the catalyst label 7555 beyond its derived borrowable set.  The targeted interaction list supplied

```
{55,95} -> {35,5035},
{1079,5035} -> {1007,7555}.
```

All three inputs 55,95,1079 were already borrowable.  Thus the last required catalyst is available under the actual restricted palette.  The separate repair certificate checks the full sequence and returns the same borrowed word; this local observation alone is not the end-to-end certificate.
