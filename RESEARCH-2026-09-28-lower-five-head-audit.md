# The lower five-head exchange meets long growth but does not balance vertices

The proved Q move uses

```text
n=9223+16320h,  c=3689+6528h,  d=5425+9600h,  h>=0,
r_(5n) r_c = r_n r_d,  c,d<n.
```

It is a one-pair identity under availability of `c`, not a repair of the
inverse-five certificate.  The latest family checkpoint and the negative
inventory correctly leave uniform borrowing, target selection, and a
well-founded repair measure open.

## Ordinary dynamics on this progression

Put `k=(n-7)/64=144+255h`.  The actual first six shortcut states are the
common `64k+7` prefix and end at

```text
p=T^6(n)=81k+10=11674+20655h,
p+1=11675+20655h.
```

All first six states exceed `n`.  If `h` is even, `p` is even and
`T^7(n)=p/2<n`, since `2n-p=6772+11985h>0`.  If `h≡1 (mod 4)`, then
`p+1≡2 (mod 4)`, so the next odd step is followed by an even step and
`T^8(n)=(3p+1)/4<n`, since `4n-(3p+1)=1869+3315h>0`.  The only
subprogression not covered by these short descents is `h≡3 (mod 4)`.

There is no uniform bound on first descent over the full lower family.
For every `j>=6`, the odd coefficient `20655` gives a unique residue

```text
h_j ≡ -11675 * 20655^(-1) (mod 2^j)
```

such that `p+1=2^j s` with positive integer `s`.  For any nonnegative `h`
in that residue, the next `j` states satisfy

```text
T^(6+i)(n)=3^i 2^(j-i) s-1,       0<=i<=j.
```

Every input for `i<j` is odd, and the states strictly increase from
`p>n`.  Hence no state through step `6+j` is below `n`.  At `j=6`,
`20655≡47`, `11675≡27 (mod 64)`, so `h_j≡43 (mod 64)`; equivalently
`k≡37 (mod 64)`.  This is an intersection with the long-growth *residue
class* and supplies a long-growth subfamily inside the lower Q family.
It does not assert equality with the previously selected least-representative
stress inputs.  In contrast, the virtual endpoint is again `7 mod 64`
only when `k≡10 (mod 64)`, or `h≡6 (mod 64)`.  That entire intersection
has even `h` and already descends at step 7.  The Q family is therefore not
merely an easy-prefix class, but its self-return slice is easy.

## What the exchange does to vertex balance

For an odd factor use boundary `B(r_u)=e_u-e_(T(u))`.  In this family,

```text
T(c)=5534+9792h,     T(d)=8138+14400h,
T(n)=13835+24480h,   T(5n)=69173+122400h.
```

The eight involved vertices are strictly ordered, for every `h>=0`, as

```text
c < d < T(c) < T(d) < n < T(n) < 5n < T(5n).
```

Thus the two-factor boundaries each have `l1` norm 4, and their difference
is the eight-charge relation

```text
B(r_n r_d)-B(r_(5n) r_c)
 = e_n+e_d+e_(T(5n))+e_(T(c))
   -e_(T(n))-e_(T(d))-e_(5n)-e_c,
```

with `l1` norm 8.  The output introduces the genuine first edge from `n`,
but leaves `d`; it also removes the edge from `5n` that joined the next
virtual edge at `T(5n)`.  Scalar equality alone gives no decrease of a
vertex-defect norm.  Charges from the rest of the virtual certificate and
a legally built borrowing word could cancel some of these eight terms, so
this calculation is not a no-repair theorem.  A family repair still needs
an explicit context and a decreasing, target-free balance argument.

## A necessary cost for borrowing the growing label

Any positive unit word `2^t ∏_(i=1)^q r_(u_i)=1` has every odd `u_i`
coprime to 3, since `v_3(r_u)=v_3(u)>=0`, and `t<=q`, since each
`r_u>=1/2`.  More strongly, bounded `q` forces bounded labels, independent
of the restricted palette.  Here is an effective proof.  Sort
`u_1<=...<=u_q` and write
`∏(3+1/u_i)=2^(t+q)`.  After a prefix of `k<q` labels, let
`P=∏_(i<=k)(3u_i+1)`, `U=∏_(i<=k)u_i`, `r=q-k`, and
`A=2^(t+q)U`.  The remaining product is `A/P>3^r`, so the positive
integer `A-3^r P` is at least 1.  Its gap above `3^r` is therefore at
least `1/P`.  If `v=u_(k+1)`, telescoping the remaining product gives

```text
1/P <= ∏_(i>k)(3+1/u_i)-3^r <= r*4^(r-1)/v.
```

Set `B=q*4^(q-1)` and `C=3B+1`.  Then `v<=BP`, while the next prefix
product satisfies `P'<=C P^2`.  Starting at `P_0=1` gives
`P_k<=C^(2^k-1)` and, for `q>=1`,

```text
max_i u_i <= C^(2^(q-1)).
```

Consequently a legal unit word containing `c(h)=3689+6528h` must use an
unbounded number of odd factors as `h` grows.  The inequality gives a very
coarse effective lower growth rate; it does not exclude borrowing with a
lengthening derivation.  A fixed affine list of positive labels is even more
directly impossible as a unit: every nonconstant `r_(ah+b)` strictly
increases with `h`, while the fixed factors of 2 do not change.


## Formal target and scope of the effective bound

`Obstructions/UnitSupportBound.lean` proves a general denominator-bounded
rational-product theorem, using a recursive bound and a looser local estimate than the
displayed closed-form argument.  Neither final bound uniformly dominates the other.  Its `productLabelBound q B` has base value zero at q=0; at q+1,
put `m=(q+1)*4^(q+1)*B` and take the maximum of m and
`productLabelBound q (B*(3*m+1))`.  Removing a least label is exactly the
prefix argument above.  The unit corollary takes denominator bound B=1.
The closed form in this note remains a paper calculation.


## A tempting connected-pair composition fails at parity

The older neutral identity with `k=5,t=s` is the formal rational equation

```text
r_(17s) r_b = r_(25s) r_e,
b=(255s+5)/2=3n+1,   e=(75s+1)/2=T(25s),
n=(85s+1)/2.
```

It is a legal odd-generator exchange only when `s≡3 (mod 4)`, the condition
`kt≡3 (mod 4)` in the earlier theorem.  Indeed, for odd `s`, the
numerators defining both `b` and `e` are `3s+1 (mod 4)`, while the
numerator defining `n` is `s+1 (mod 4)`.  Thus:

```text
s≡1 (mod 4): n odd, b and e even;
s≡3 (mod 4): n even, b and e odd.
```

The lower five-head family needs odd `n`, so no parameter admits both Q
moves as legal odd-generator substitutions.  On its `s≡1` branch, `b` and
`e` are genuine even vertices, but each actual shortcut edge has ratio
`u/T(u)=2`, not the formal value `2u/(3u+1)` used in the neutral
identity.  Replacing both formal companion factors by actual even edges
would assert `2r_(17s)=2r_(25s)`, which is false.  Even changing the
number of pure even edges cannot fix this two-odd-label comparison:

```text
r_(17s)/r_(25s)=(1275s+17)/(1275s+25),
1/2 < r_(17s)/r_(25s) < 1.
```

No integer power of 2 equals that ratio.  On `s≡3 (mod 4)` the old
neutral Q move is legal, but `n` and `5n` are even, making the five-head
move illegal and outside the `n≡7 (mod 64)` family.  The apparent
composition is therefore invalid reuse of the old odd-pair identity.
A more elaborate repair with new odd factors is not excluded, but it would
need a new legal relation and a borrowing/endpoint proof.
