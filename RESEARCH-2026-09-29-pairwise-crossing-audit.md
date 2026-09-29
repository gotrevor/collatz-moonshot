# Time-indexed pair crossings: a conditional height bound, no exclusion

This pass read `RESEARCH-2026-09-28-pair-ordering.md`,
`RESEARCH-2026-09-27-pair-denominators.md`, `FRONT-B-ROUTES.md`, and the
pairwise/Front-B negative entries in `APPROACHES.md`.  The earlier inversion
count and Vandermonde transport are identities or weak bounds; rotation
integrality is already a single-word condition.  I tested one different
observable on paper, retaining the *time of the first mixed-parity meeting*
of a pair and the integer gap at that time.

Let `T(x)=x/2` for even positive integers and `T(x)=(3x+1)/2` for odd ones.
Take distinct integer cycle vertices `x,y` and follow both for `h` shortcut
steps.  Suppose their parities agree at each time `0,...,h-1`, and exactly `a`
of these common parities are odd.  Write `Delta_t=|T^t(x)-T^t(y)|`.  Then

```
Delta_h = (3^a / 2^h) Delta_0,
2^h | Delta_0,                    3^a | Delta_h.       (1)
```

The first equality follows by subtracting equal-branch affine maps.  Since
`Delta_h` is an integer and `gcd(3^a,2^h)=1`, the other two claims follow.
This is the dyadic prefix-collision fact with its surviving `3^a` factor
kept at the *later* time.  It is not a new word-admission test.

Suppose the pair is mixed at time `h`, with lower odd state `o`, upper even
state `e`, and their next images reverse order.  The exact crossing condition
is `o<e<3o+1`.  As `e` and `3o+1` are even, `e<=3o-1`; hence

```
3^a <= e-o <= 2o-1,              o >= (3^a+1)/2.     (2)
```

This is a **conditional** time/order/integer-spacing inequality.  A crossing
after many shared odd steps cannot occur at a small odd vertex.  For a
positive integer `5x+1` shortcut, the same proof gives `5^a | Delta_h` and
`5^a <= e-o <= 4o-1`.  Thus the mechanism is not selective against the known
positive integer `5x+1` cycle `1110000`.

For a rational `3x+1` cycle with common reduced denominator `d`, the same
subtraction gives `Delta_h=3^a z/d` for an integer `z`; it does **not** give
`3^a | Delta_h` in the integer sense.  The positive rational `11111000`
control already has minimum real pair gap `69/13>1`, so replacing (1) with
only `Delta_h>=1` would miss the arithmetic distinction.  The smaller
positive rational `00101` control has states `(28,14,7,22,11)/23` and six
mixed inversions; it demonstrates that cyclic order and crossing frequency
alone are insufficient.  No CLI run was needed for these exact controls;
both are recorded in the cited repository notes.

**Proved implication:** (2) holds for every crossing preceded by `a` shared
odd steps in a positive integral cycle.  **Open premise needed for exclusion:**
every nontrivial primitive positive integral cycle would have to contain a
pair with a crossing whose shared-odd count `a` exceeds
`log_3(2o-1)` at its lower odd endpoint `o`, or satisfy another uniform
inequality that forces such a pair.  I found no reason for this.  The cycle
may place long shared-prefix pairs at large vertices, and (2) then allows
them.  In particular, (2) gives no upper bound on the cycle denominator
`D=2^b-3^a`, no bound on circuit count, and no Front-B exclusion.

This pass therefore identifies a genuine conditional integer inequality but
**no candidate proof mechanism** for the needed premise.  It does not reopen
the retired generic pairwise-transport lane.
