# The exceptional `q1` slope: sparse merging and arbitrarily long separation

Here `T(x)=x/2` for even positive integers and `T(x)=(3x+1)/2` for odd
positive integers.  The hard-64 families in the repository are

\[
n(s)=25542881863+39026668800s,\qquad
q(s)=q_1(s)=1795983881+2744062650s,\qquad s\geq0.
\]

They satisfy `128q=9n+1`.  Because the slope of `n(s)` is divisible by
`128`, the first seven parity bits are the fixed word `1110101`, with
`T^7(n)=(243n+283)/128=27q+2`.  The prior affine-slope audit leaves this pair exceptional:
the coefficient ratio is supported only on 2 and 3.  This note resolves whether a uniform finite coalescence bound can cover the
whole family; it does not classify every merging subprogression or address
arbitrary-depth convergence.

## An infinite coalescing subprogression

For every positive odd `q ≡ 105 (mod 2048)`, the first eleven parity bits,
in time order, are as follows.  Each row is an exact affine branch formula;
the parity word is admitted throughout the stated residue class because
the first eleven shortcut parities depend only on the input modulo `2^11`.

| initial value | parity word | odd steps | exact eleventh iterate |
|---|---|---:|---|
| `q` | `10111100100` | 6 | `(729q+1279)/2048` |
| `27q+2` | `10000010001` | 3 | `(27(27q+2)+1225)/2048` |

The two numerators are identical: `27(27q+2)+1225=729q+1279`.
For a small independent arithmetic anchor, the admitted trajectory of
`105` is `105,158,79,119,179,269,404,202,101,152,76,38`, while that of
`2837=27·105+2` is
`2837,4256,2128,1064,532,266,133,200,100,50,25,38`.

The affine `q(s)` reaches this residue precisely when `s ≡ 240 (mod 1024)`:
after dividing `q_0+D s ≡ 105 (mod 2048)` by 2, `D/2=1372031325`
is invertible modulo 1024, and direct substitution gives the residue 240.
Consequently, for every nonnegative `t`, with `s=240+1024t`, actual positive
shortcut orbits satisfy

\[
T^{18}(n(s))=T^{11}(q_1(s))
  ={729q_1(s)+1279\over2048}.
\]

This is *jointly admitted* coalescence for an infinite sparse subfamily,
so an attempted universal fixed-word obstruction for the `q1` pair is false.
The common value is below `q` (indeed `(729q+1279)/2048<q` for every
`q>1`), so it is a direct 18-step descent for this class.  It is an
easy bounded class, not a recursive mechanism for the whole family.

## An infinite hard-shadow progression at every finite depth

There is a stronger obstruction to covering this family by bounded
coalescence: for every `K≥1`, infinitely many parameters have both **no
descent of `n` through step `K`** and **no meeting of its first `K` iterates
with any of the first `K` iterates of `q`**.  This is a finite-depth statement;
the chosen congruence depends on `K`.

Choose `L≥max(K+2,4)` and put `w=9q+1=2^L u`, where `u>0` is an integer.
Such `s` form an infinite arithmetic progression: `9q_0+1` is even and
the coefficient `9D` has 2-adic valuation one, so the congruence has a
unique solution for `s` modulo `2^{L-1}`.  For example, at `L=8` this is
`s ≡ 107 (mod 128)`.

The fixed first-six parity word of `n` is `111010`.  Its iterates through
step six are

\[
{3n+1\over2},\quad {9n+5\over4},\quad {27n+19\over8},\quad
{27n+19\over16},\quad {81n+73\over32},\quad
{81n+73\over64}=18q+1=2w-1.
\]

All six are strictly greater than `n` (the hard-64 `n` is positive and
larger than one).  The last value is congruent to `−1` modulo `2^{L+1}`;
its next `L+1` branch steps are odd and satisfy

\[
T^{6+r}(n)=3^r2^{L+1-r}u-1>n
\qquad(0\leq r\leq L+1).
\]

The inequality follows because these odd steps strictly increase from
`T^6(n)>n`.

For the `q` orbit, `q` and `T(q)` are odd, and

\[
T^2(q)={9q+5\over4}=1+\delta_0,
\qquad\delta_0={w\over4}>0.
\]

Its following steps shadow the `1↔2` cycle.  Whenever the displayed
exponent is at least two, put
`δ_r=3^r2^{L-2-2r}u=(3/4)^rδ_0`.  Then

\[
T^{2+2r}(q)=1+\delta_r,\qquad
T^{3+2r}(q)=2+\tfrac32\delta_r,
\qquad \delta_{r+1}=\tfrac34\delta_r.
\]

The first value is odd and the next is even, so these are admitted actual
shortcut steps.  The choice `L≥K+2` guarantees every step through `K`
is covered.  Since the peaks decrease and the initial `q,T(q),T^2(q)`
are also below the first peak, every `j≤K` satisfies

\[
T^j(q)\leq T^3(q)={27q+19\over8}
  <{128q-1\over9}=n.
\]

The last strict inequality reduces to `179<781q`, true for every positive
integer `q`.  Thus `T^i(n)≥n>T^j(q)` for all `0≤i,j≤K`, and
`T^i(n)>n` for `1≤i≤K`.  This gives an explicit finite-depth adversary
to any fixed coalescence or descent cutoff.  It says nothing about later
iterates of each chosen parameter, or about a single parameter shadowing
for infinitely many steps.

The earlier slope audit found that each of the other nine auxiliary
families has a coefficient ratio with a prime outside `{2,3}`.  For fixed
depths, every parity-word pair against one of those families has unequal
affine slopes and hence meets for at most one parameter.  There are only
finitely many word pairs and targets in a finite menu.  Avoid those finitely
many parameters inside the infinite hard-shadow progression above: **no
finite menu of bounded-depth splices into any of the ten auxiliaries covers
all hard-64 parameters**.  This is a scope test for a finite menu, not an
obstruction to an adaptive repair whose depth grows with the parameter.

## Comparison: easy fixed-point shadow also evades bounded merging

Put `H(q)=27q+2`.  Its 2-adic fixed point is `−1/13`, since
`H(q)−q=2(13q+1)`.  For any `K≥1`, there are arbitrarily large nonnegative
parameters `s` satisfying

\[
13q(s)+1\equiv0\pmod{2^K}.
\]

Indeed `q_0` is odd, hence `13q_0+1` is even; the coefficient `13D` has
2-adic valuation exactly one.  Dividing by 2 leaves a linear congruence
with odd coefficient and therefore a unique solution modulo `2^{K-1}`.
For these `s`, `H(q)−q` is divisible by `2^{K+1}`.  The two actual orbits
have the same parity at each of their first `K` steps.  Inductively, after
`j≤K` steps their positive difference is

\[
T^j(H(q))-T^j(q)
  ={3^{a_j}(H(q)-q)\over2^j}>0,
\]

where `a_j` is their common number of odd steps.  Divisibility by
`2^{K+1-j}` keeps the next parity common for `j<K`.  Hence **there is no
synchronous coalescence `T^j(H(q(s)))=T^j(q(s))` for `j≤K`** on this
infinite parameter progression.

**These avoidance witnesses themselves have a fixed, short descent.**
Choose the congruence above at depth at least `8`, even when the meeting
bound is smaller.  The condition `13q+1 ≡ 0 (mod 256)` is exactly
`q ≡ 59 (mod 256)`, or `s ≡ 109 (mod 128)` in the hard-64 family.  The
2-adic fixed point `−1/13` has the first-eight parity word `11011000`:
its formal 2-adic branch iterates are
`(−1,5,14,7,17,32,16,8,4)/13`.  Since
`H(q)−(−1/13)=27(q+1/13)`, both `q` and `H(q)` have that word whenever
`q ≡ 59 (mod 256)`.  The branch formula is `T^8(x)=(81x+85)/256`.
Combining it with the known seven-step prefix gives

\[
T^{15}(n)=T^8(H(q))={2187q+247\over256}
  ={19683n+33803\over32768}<n
\]

for every member of this positive hard-64 subfamily.  Thus failure of
bounded *merging with `q1`* occurs here alongside direct 15-step descent;
it is not evidence that these labels are difficult for Collatz induction.

This also rules out a *uniform bounded-depth coalescence cover* of all
`n(s)` by `q(s)`, even if the two times vary with `s`.  Here is a quantitative
version.  For a parity word of length `l` with `a` odd steps, write its
branch as `(3^a x+β)/2^l`; its nonnegative intercept satisfies
`β≤3^l−2^l<3^l` (the all-odd word maximizes it).  Suppose actual branches
of lengths `i,j≤K`, with odd counts `a,b` and intercepts `β_i,β_j`, meet
at `n,q`.  Substitute `n=(128q−1)/9` and clear denominators to obtain

\[
\bigl(128\cdot3^a2^j-9\cdot3^b2^i\bigr)q
 =3^a2^j-9\beta_i2^j+9\beta_j2^i.
\]

If the integer coefficient on the left is nonzero, the intercept bound
gives `q≤10·3^i2^j+9·3^j2^i≤19·6^K`.  If it is zero, unique
factorization into powers of 2 and 3 forces `i=j+7` and `a=b+2`.  The
known seven-step prefix then turns the meeting into
`T^j(H(q))=T^j(q)`, which the fixed-point congruence above excludes for
`j≤K`.  Choose any `s` in the congruence class at depth `max(K,8)` with
`q(s)>19·6^K`.  Therefore, for each fixed `K`, infinitely many `s`
have **no** equality `T^i(n(s))=T^j(q(s))` with `0≤i,j≤K`.

The hard-shadow result excludes uniform bounded **coalescence or first
descent** over the whole parameter family.  It coexists with the explicit
easy coalescing progression above.  All congruences here depend on the
chosen finite depth; nothing rules out meetings or descent at depths
growing with `s`, and no divergent orbit is produced.

## Appendix: a tempting joint rank fails at the first odd exit

The hard-shadow trajectories have aligned frontiers
`A_r=T^(6+2r)(n)` and `B_r=T^(2+2r)(q)` during their joint phase.  The
formulas above give the exact relation

\[
A_r+1=8\cdot3^r(B_r-1).
\]

The 2-adic precision of `B_r−1` decreases by two per round, while the
multiplier `8·3^r` grows.  A candidate integer rank is
`R(A,B)=(A+1)(B−1)^3`.  In an admitted round where `A` takes two odd
steps and `B` takes odd then even, `A+1` is multiplied by `9/4` and
`B−1` by `3/4`, giving the exact contraction
`R_next/R=243/256`.  This contraction **does not survive the first exit
in one parity class**.

For the separated phase assume `L≥2`.  Write `L=v₂(9q+1)` exactly, so `u=(9q+1)/2^L` is odd.  If `L=2m`, the
first exit frontier is `r=m−1` and `B=1+v` with `v=3^{m−1}u` odd.  Thus
`B` is even, rather than the expected odd.  The first actual step still
contracts `R`, by the factor
`(3/16)((v−1)/v)^3`.  After two actual steps, the factor is

\[
\frac{R_{\mathrm{after}}}{R_{\mathrm{before}}}=
\begin{cases}
9(3v+1)^3/(256v^3),&v\equiv1\pmod4,\\
9(v-3)^3/(256v^3),&v\equiv3\pmod4.
\end{cases}
\]

For this hard-64 `q(s)`, `v≥27`: if `m≥4`, this follows from
`3^{m−1}≥27`; if `m≤3`, it follows from
`u=(9q+1)/2^{2m}≥(9q_0+1)/64>27`.  Both displayed factors are then
strictly below one.  The `v≡1` factor is decreasing in `v`, and at `27`
its comparison is `9·82³<256·27³`.

If `L=2m+1`, the first exit frontier has `B=1+2v`,
`v=3^{m−1}u` odd.  Its first step is odd, but
`T(B)=2+3v` is odd rather than the expected even.  The intermediate rank after that first step has increased by

\[
\frac{R_{\mathrm{after\ one}}}{R_{\mathrm{before}}}
=\frac32\left(\frac{3v+1}{2v}\right)^3>\frac{81}{16}.
\]

An increase at an intermediate step alone would not refute a rank on two-step blocks.  Here the complete exit block fails too: after the next actual odd step the rank has increased by the still larger factor
`(9/4)((9v+5)/(4v))^3>6561/256`.  This is an infinite counterexample
family within the actual `q_1(s)` parameters: `s≡27 (mod 32)` gives
`v₂(9q(s)+1)=5`, so all such parameters reach this odd-`L` exit.

Finally, `R(A,1)=0` even when `A≠1`.  Any rank intended to prove a joint
terminal condition must address that degeneracy as well.  The exact
regular-phase contraction alone supplies no valid global ordinal rank.
The valuation `v₂(B−1)` can rank this finite shadow phase, but it reaches
zero or one at exit while `8·3^r` has grown; an exit argument needs a
separate state constraint.  None is established here.

## Formalized scope and persistent instruments

[Q1Coalescence.lean](CollatzMoonshot/Obstructions/Q1Coalescence.lean) proves the actual-orbit power-of-two offset formula, the near-1 cycle bound, both eleventh-iterate formulas on `105+2048t`, the seventh-step hard-family identity, the 18-step merge and descent on `s=240+1024t`, and the all-depth ordered-separation theorem.  Its explicit corollary is

```
∀ K, ∃ s, ∀ i ≤ K, ∀ j ≤ K,
  T^[i](n(s)) ≠ T^[j](q1(s)).
```

The same chosen parameter has `n(s)≤T^[i](n(s))` and `T^[j](q1(s))<n(s)` for all those times.  This is an unbounded-depth theorem about actual positive integer orbits, not a finite search extrapolation.  The negative-fixed-point comparison and its 15-step descent argument above remain paper-only.

`experiments/repair_family.py q1-pair-branch` partitions the parameter into exact residue progressions and advances their affine forms, declaring a connection only when both affine coefficients agree.  It finds the depth-11 class and returns the entire unresolved frontier when a depth or branch cap is reached.  `q1-pair-shadow K` constructs the hard ordered-separation congruence; `--variant carry13` retains the easy-descent comparison.  The persistent real-CLI suite has 16 passing tests, including independent small parity paths, residue anchors, and a frontier-coverage check.  The existing Lean CI audit consumes the frozen definitions and both the positive and negative endpoint types.

## What is closed, and what remains

No finite menu of bounded-depth splices into the `q1` orbit covers the whole hard64 family: take the maximum depth of the proposed menu and apply ordered separation.  Combined with the earlier nine incompatible-slope families, the paper argument also excludes a bounded-depth menu choosing among all ten supplied auxiliary orbits.  For each fixed bound, those other nine families have only finitely many exceptional parameters, whereas the hard shadow supplies an infinite residue progression avoiding `q1`.  This ten-family combination is not yet a separate Lean theorem.

The excluded quantifier order is `∃K ∀s ∃i,j≤K`.  The statement `∀s ∃i,j` remains open here; allowing depths to grow with `s` escapes this obstruction.  In particular, this result does not rule out an ordinal-ranked adaptive repair.

There is already an exact variable-length description of the separated phase.  Write `9q+1=2^L u` with `u` odd.  While `L-2-2r≥2`, set

```
A_r = T^(6+2r)(n),    B_r = T^(2+2r)(q).
A_r + 1 = 8*3^r*(B_r-1).
```

The next pair of steps changes the multiplier `8*3^r` to `8*3^(r+1)`, while reducing the remaining binary precision by two.  A rank on that precision alone terminates this phase; it does not handle the exit with its enlarged multiplier.  A successor mechanism must specify and justify that exit transition, or produce a different exact signed boundary to a known convergent vertex.  Neither another fixed-depth scan nor another sparse coalescing class supplies it.
