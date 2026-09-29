# Quadratic exchanges at the artificial `5n` head

For positive odd labels, write `r_u = u/T(u) = 2u/(3u+1)`.  A proposed pair move
`{5n,c} -> {n,d}` preserves the product exactly when

```text
d (15n + 1 - 12c) = 5c (3n + 1).                 (Q5)
```

This follows by clearing positive denominators and cancelling `n` from
`r_(5n) r_c = r_n r_d`.  It is precisely the `a=5n, b=c, new c=n, new d=d`
instance of the generic quadratic relation in
`RESEARCH-2026-09-28-quadratic-divisors.md`.  It is not an instance of the
older connected-pair neutral rule in
`RESEARCH-2026-09-27-arithmetic-lifts-followup.md`: that rule takes its second
input to be the actual successor `T(5n)`, whereas these families supply a
separate auxiliary label.

The observed 1031 identity extends rationally by setting

```text
c = (224n + 1)/221,
15n + 1 - 12c = 209(3n + 1)/221,
d = 5(224n + 1)/209.
```

The integer progression `n=1031+46189t`, `c=1045+46816t`,
`d=5525+247520t` satisfies these equations.  For integer `t>=0`, all three
labels are positive.  `n` is odd iff `t` is even.  Since `1031≡7` and
`46189≡45 (mod 64)`, the original `n≡7 (mod 64)` condition is equivalent to
`t≡0 (mod 64)`.  On that subprogression, `n,c,d,5n` are all outside `3ℕ`
exactly when `t≡0 (mod 192)`: with `t=64j`, their residues modulo 3 are
`2+j,1+j,2+2j,1+2j`, respectively.  Thus the clean three-free family is

```text
n=1031+8868288h,  c=1045+8988672h,  d=5525+47523840h,  h>=0.
```

Here `c-n=14+120384h>0`.  The move can use a borrowed `c` at `h=0`, but
nothing here constructs a unit containing `c` uniformly.  Its height grows
above `n`, so ordinary induction on smaller heads does not supply it.

A different rational line on (Q5) is

```text
n=(85s+1)/2,  c=17s,  d=25s.
```

Indeed `15n+1-12c=(867s+17)/2`, so both sides of (Q5) equal
`25s(867s+17)/2`.  For positive `s≡1 (mod 4)`, all labels are positive odd.
The condition `n≡7 (mod 64)` is equivalent to `s≡89 (mod 128)`, using
`85^(-1)≡125 (mod 128)`.  Writing `s=89+128j`, the four labels avoid `3ℕ`
exactly when `j≡1 (mod 3)`.  Consequently the clean family is

```text
s=217+384h;
n=9223+16320h,  c=3689+6528h,  d=5425+9600h,  h>=0.
```

Now `n-c=5534+9792h>0` and `n-d=3798+6720h>0`.  This makes a
height-induction hypothesis relevant to borrowing `c`, if that hypothesis
actually supplies a legal unit word containing `c`.  After the exchange,
`d` remains in the virtual certificate; the one Q move is not a whole repair.
Neither family by itself proves a Collatz descent mechanism.

## Why the observed full script does not deform with this one row

The 1031 witness also uses the nontrivial row
`{25,7733} -> {37,77}`.  Here `7733=T(5*1031)`.  If a proposed
symbolic lift keeps `25`, `37`, and `77` fixed and substitutes
`T(5n)=(15n+1)/2` for `7733`, equality of that row forces
`r_(T(5n))=r_7733`.  The function `u ↦ 2u/(3u+1)` is strictly increasing
on positive `u`, so `T(5n)=7733` and hence `n=1031`.  More generally, the positive-divisor argument behind the repo's exact
`quadratic-neighbors` search gives only finitely many nontrivial positive-odd
interactions for a fixed first label `25`; it cannot supply an unbounded
affine family while `25` stays fixed.  Therefore the
single legal Q family above does not deform all 16 rows of the observed
repair script.  Any family-level repair must replace this bridge and certify
its unit borrowing and endpoint separately.
