# The full odd-run macro after the `q1` exit

This continues `RESEARCH-2026-09-29-q1-phase-exit.md` with the actual
target's remaining forced steps.  It is a paper test of recursive closure,
not an orbit census or a claim against adaptive repair.  Fix an **exact odd**
valuation `L=2r+3` of `9q+1=2^L u`, with `u>0` odd, in the hard-64 family.
Put `H=3^(r+2)`.  At the completed two-step odd exit, the actual pair is

\[
A=4\cdot3^{2r+2}u-1,\qquad C=(Hu+7)/2.
\]

## The target's complete forced run

The exit value has `v₂(A+1)=2`.  Its next two steps are necessarily odd;
after them the target is the even number

\[
T^2(A)=H^2u-1.
\]

Let `k=v₂(H²u−1)≥1`, and then take the complete following even run.
The next odd target frontier is

\[
X=F_H(u):={H^2u-1\over2^k}.
\]

This is the exact run-to-run parameter map.  It has no monotone sign on
the actual hard-family parameter domain.  For fixed `L`, write its exact
valuation class as `s=s_L+2^L t`; then
`u(t)=u_0+2Et`, where `E=12348281925` is odd.  The affine expression
`H²u(t)−1` has coefficient `2H²E` of 2-adic valuation one.  Therefore
**every** exact `k≥1` occurs for infinitely many `t`.

In particular, `k=1` exactly when `u≡3 (mod 4)`, an infinite half of
this progression because `E` is odd.  Then
`X=(H²u−1)/2>u`; more strongly, on the hard family

\[
n={2^{L+7}u-137\over81},\qquad X>n.
\]

The last inequality follows by multiplying out:
`81H²−2^{L+8}=3^{2r+8}−2^{2r+11}>0`, while the constant side is
`81−274<0`.  Conversely, choose exact `k` with `2^k>H²`.
Then `X<u<n`, so infinitely many fixed-`L` parameters get a genuine
target descent at this macro endpoint; `n>u` follows from
`2^{L+7}≥1024` and `u≥1`.  Neither `u` itself nor the target's numerical size decreases for
every completed run.  The calculation supplies no decreasing replacement
for the initial precision `L`; it does not exclude every possible function
of these data.

The branch does not collapse to a small set of odd outputs.  For each
fixed exact `k`, the parameters are one class `t=t_k+2^k z`.  Along it

\[
X(z)=X_0+2H^2E z.
\]

Thus `X` visits every odd residue modulo every `2^j` as `z` varies.
The compressed map `F_H` has arbitrary finite target parity behavior
after this run, even at fixed `L` and `k`.

## Synchronized full affine state

Keep the auxiliary synchronized while the target takes its two odd
steps and `k` even steps.  Let its admitted word of length `k+2` have
`b` odd steps and branch intercept `β`, so the new auxiliary is
`Y=(3^b C+β)/2^(k+2)`.  Substituting the exit formulas yields the exact
completed-block state

\[
X={H^2u-1\over2^k},\qquad
Y={3^bHu+7\cdot3^b+2\beta\over2^{k+3}},
\]

or, eliminating `u`,

\[
2^{k+3}H Y
 =3^b2^kX+3^b(7H+1)+2H\beta.
\]

The offset depends on the actual auxiliary word.  It is not a restart
of `A+1=8·3^j(B−1)` with a new exponent.  This equation is a complete
affine branch description, but by itself it supplies neither a smaller
parameter nor a terminal connection.

The synchronization does not remove the auxiliary's future parity
freedom.  On an exact-`k` parameter class, `C` advances by
`2^k c` per `z`, where `c=9·3^rE` is odd.  Fixing the auxiliary's word
through `k+2` steps restricts `z` to one residue modulo four.  On each
nonempty such class the resulting `Y` advances by `3^b c`, an **odd**
step.  Hence `Y` again visits every residue modulo every `2^j` and
admits every finite subsequent parity word.  The coupled equation may
still carry useful arithmetic, but a finite parity suffix is not
inherited from the long initial shadow.

## Minimum length of a symbolic canonical reset

There is also a limited, exact obstruction to resetting the *old*
canonical class by a fixed pair of parity words.  Suppose a `d`-step
branch from `A` with `a` odd steps and intercept `β_A`, and an `e`-step
branch from `C` with `b` odd steps and intercept `β_B`, satisfy

\[
T^d(A(u))+1=8\cdot3^j(T^e(C(u))-1)
\]

as an affine identity throughout an infinite parameter progression on
which both words are admitted.  Comparing the `u` slopes forces
`d=e` and `j=r+a−b`.  Comparing constants then gives

\[
N_A:=\beta_A+2^d-3^a
 =4\cdot3^j(7\cdot3^b+2\beta_B-2^{d+1}).
\]

Starting at zero, `N_A` changes by `N→N+2^h` on an even bit at time
`h`, and by `N→3N` on an odd bit.  Thus `0≤N_A<3^d`, and `N_A=0`
exactly for the all-odd word.  If `r≥2d`, then `j≥r−d≥d`; the right
side is divisible by `4·3^d`, so `N_A=0`.  The remaining equation would
make the auxiliary branch send `7/2` to `1`, impossible because
`(7·3^b+2β_B)/2^{d+1}` has odd numerator.  Therefore any **symbolic,
full-progression** reset to this canonical class requires `d=e>r/2`.
This does not exclude an isolated parameter re-entry, a different
offset state, or an adaptive word whose length scales with `r`.

The full-run calculation gives no recursive rank.  It shows the exact
additional obligation: control an affine offset whose next parity
word is unrestricted, through a block long enough to overcome the
`r/2` reset barrier or into a genuinely different state class.  A
completed-block rank remains possible, but extending the initial
shadow calculation alone does not provide one.


## Reset accounting for the polynomial weight

At the initial normalized pair write `d=(9q+1)/4`, a positive integer.
Then `(A0,B0)=(8d-1,d+1)` and the candidate weight is exactly

```
R(A0,B0)=8*d^4=(9q+1)^4/32.
```

Consequently, returning to a fresh normalized pair with a strictly smaller
weight is equivalent to returning with a smaller `d`, hence a smaller `q`
and a smaller original `n` in the hard family.  The intermediate shrinkage
of the auxiliary is not free credit that survives a reset to a large fresh
auxiliary.  This identifies the missing numerical descent in this specific
restart strategy.  It does not rule out a richer inherited state, a different
weight, or an ordinal rank which preserves information through reset.

The corrected terminal weight `(A+1)*B^3` would avoid vanishing at `B=1`,
but on normalized starts it is still a strictly increasing polynomial
`8d*(d+1)^3`.  Merely replacing the vanishing factor therefore does not
remove the reset cost.

## Exact diagnostic and evidence levels

`experiments/repair_family.py q1-run-exit L u` executes only the explicit
finite phase, two remaining odd steps, and the following full halving run.
It reports the actual-family membership and the resulting comparisons to
both `u` and the original `n`.  Its persistent external CLI tests include
generic controls `L=3,u=3` giving `X=121>u`, and `L=3,u=49` giving
`X=31<u`.  A separate actual hard-family anchor is `s=27`,
`L=5,u=21342846215`, `n=1079262939463`, with
`X=7779467445367>n`.

The all-valuation progressions, synchronized output equation, and symbolic
reset-depth lower bound above are paper arguments.  A bounded proof task in
`KICKOFF-2026-09-29-q1-reentry.md` targets the actual two-step exit, immediate
canonical nonclosure, the target's next forced run, one-halving expansion,
and the normalized-rank reset equivalence.  Its completion must be checked
before describing those statements as formalized.

The [full affine-offset audit](RESEARCH-2026-09-29-odd-exit-offset-audit.md) records the exact four-parity state update, pointwise failure of the first two synchronous resets, and the smaller alternate auxiliary.  These additional calculations remain paper-side.
