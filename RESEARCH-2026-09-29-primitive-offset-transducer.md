# Inherited primitive offsets after the hard-family odd exit

This is a paper audit of a proposed completed-block rank, using the actual hard family of `CubicPeel.lean`.  It does not assume convergence of an unknown frontier.  The relation below is **inherited from an affine parameter family**; it is not reselected from each numerical pair.

Let the aligned pair be `(A,B)=(8d−1,d+1)`, with `d=(9q+1)/4`.  Its inherited relation is `A−8B=−9`.  After the odd phase and its exit, the repository's formulas give

```
A=36·9^r·u−1,       B=(9·3^r·u+7)/2,
A−8·3^r B=−(28·3^r+1),       r≥0, u>0 odd.
```

The displayed equations are primitive because the coefficient of `A` is one.  The absolute offset rises from `9` to `28·3^r+1`; the coefficient height changes from `8` to `8·3^r` and is unchanged when `r=0`.  Hence neither quantity is a strictly decreasing rank for this completed odd phase, including the long phases on which the previously proved scalar weight contracts.  Minimizing over *new* integer relations would erase the obstruction artificially: every numerical `(A,B)` has `(B/g)A−(A/g)B=0` for `g=gcd(A,B)`.  A useful state must carry the inherited relation or an equivalent parameter dependence.

## Exact normalized transducer

Write the inherited relation as `hA−kB=c`, normalized by an integer `b`:

```
h=3^max(−b,0),       k=8·3^max(b,0).
```

Thus `h` is odd and `k` is even, so `A mod 2 = c mod 2`; only the known auxiliary's parity must be read from its itinerary.  Let `α=A mod 2`, `β=B mod 2` (each 0 or 1), and `b'=b+α−β`.  Let `h',k'` be the same functions of `b'`.  The common integer multiplier

```
λ=h'·3^α/h=k'·3^β/k
```

is either `1` or `3`.  One actual shortcut step on both vertices gives exactly

```
2c'=λc+h'α−k'β,       h'A'−k'B'=c'.                 (1)
```

The exit state has `(b,c)=(r,−(28·3^r+1))`.  Formula (1) is deterministic once the actual auxiliary parity is supplied.  It is a projection of the two-vertex dynamics, not a terminal criterion: numerical `A=B` need not be recognizable from `(b,c)` alone.

Even the sign of `c` is not preserved on actual hard states.  At `s=7`, `q=cubicQ1(s)=21004422431`, `n=cubicN(s)=298729563463`, and `9q+1=8·23629975235`, so `r=0` and the exit pair is `(850679108459,106334888561)` with `(b,c)=(0,−29)`.  After 28 synchronized steps it is `(561383561,5684008558)` with `(b,c)=(-4,-23)`; after 29 it is `(842075342,2842004279)` with `(b,c)=(-3,+2)`.  The last equality is the exact integer check `27·842075342−8·2842004279=2`.

## An actual five-step coefficient fixed block

For a pair at `b=-3`, the relation is `27A−8B=c`.  If the target's next five parities are `11100` and the auxiliary's are `11001`, each word contains three odd steps, and direct composition gives

```
32A'=27A+19,       32B'=27B+31,
32c'=27c+265.                                            (2)
```

At `c=53`, the last equation gives `c'=53`, and `b'=b=-3`.  The affine map in (2) contracts both numerical vertices by slope `27/32` toward the nonintegral fixed pair `(19/5,31/5)`; it does **not** exhibit a positive integer orbit cycle.  On this parity branch, the target's first three steps also satisfy `8T³(A)=27A+19`, hence `T³(A)=B+9` whenever `c=53`.  The projected fixed block retains a real vertex defect of nine.

The branch occurs in the actual `s=7` hard-family pair.  At synchronized step 35 after the exit,

```
(A,B)=(1065751607,3596911667),       27A−8B=53;
```

its five-step words are exactly `11100` and `11001`.  At step 40,

```
(A',B')=(899227919,3034894220),      27A'−8B'=53.
```

Neither endpoint has `A=B` or `T³(A)=B`.  This is more than an isolated numerical coincidence.  For every `z≥0`, take `s=7+8·2^40 z`.  The exact valuation of `9·cubicQ1(s)+1` remains three, and both exit vertices agree with those at `s=7` modulo `2^40`.  A shortcut trace of length 40 depends only on the starting vertices modulo `2^40`.  Therefore the first 40 parity words, the inherited coefficient states, and the five-step fixed block at steps 35 to 40 persist on this infinite positive hard subprogression.  The vertices themselves vary affinely with `z` and remain positive.

Consequently a rank that depends **only** on `(b,c)` cannot strictly decrease over every admissible five-step block of this form.  This does not exclude a rank retaining the current vertices, carry data, a different block decomposition, or a verified boundary transition.  In particular, the pointwise terminal `A=B` must be checked in the actual vertices; the finite symbolic condition `T³(A)=B` cannot be treated as a complete convergence test.  A natural-number “fuel” attached to the projected state would need a separately proved admission and replenishment rule, the existing obstruction for inverse-basin ranks in the September 27 negative inventory.

## Expanding coefficient ray near the negative reference pair

There is a complementary exact obstruction to a coefficient rank required to decrease on *every* six-step block.  In the `r=0` hard exit put `z=9u+1`.  Then

```
A₀=4z−5,       B₀=z/2+3,       n=(1024z−2257)/729.  (3)
```

The 2-adic reference `z=0` is the negative pair `(-5,3)`.  Its first nine words are `110110110` on A and `110001010` on B, reaching `(-5,1)`.  The same fixed words applied symbolically to (3) yield

```
A₉=−5+(729/128)z,       B₉=1+(81/1024)z,
A₉+5=72(B₉−1).                                         (4)
```

Thereafter the reference words on six synchronized steps are `110110` and `101010`.  Their exact maps are

```
64A'=81A+85,       64B'=27B+37,                      (5)
```

so `A+5` grows by `81/64` while `B−1` shrinks by `27/64`.  After `j` such blocks, while the prescribed words remain valid,

```
A_{9+6j}=−5+(729/128)(81/64)^j z,
B_{9+6j}=1+(81/1024)(27/64)^j z,
A_{9+6j}+5=72·3^j(B_{9+6j}−1).
```

The primitive projected state is `b=2+j`, `c=−(5+72·3^j)`.  It moves indefinitely away from a fixed coefficient bound in the formal reference, but the reference itself is negative and is **not** a positive Collatz orbit.

For every finite `J`, however, there are positive *admissible hard-family* lifts realizing the first `9+6J` steps of these words.  In the exact `r=0` subfamily `s=7+8t`, `u=u₇+24696563850t`, so `z=z₇+222269074650t`; `z₇` is even and the slope has 2-adic valuation one.  Hence choose arbitrarily large `t≥0` with `2^(10+6J) | z`.  Then both starting vertices agree with `(-5,3)` modulo `2^(9+6J)`, which fixes the required parity words.  For these lifts, every controlled target iterate is at least `A₀=4z−5>n`.  Every controlled auxiliary iterate is at most its first-prefix maximum `B₂=8+9z/8<n` for `z>40`; the last inequality follows directly from (3), equivalently `1631z>64712`.  Thus the expanding coefficient ray is realized for arbitrarily many blocks by positive pairs with target above the original `n` and auxiliary below it.

This prevents **any well-founded rank depending only on the projected coefficient state** from strictly decreasing on every such six-step block.  For each `j`, choose a positive lift with at least `j+1` blocks.  Its `j`th block realizes the edge `(2+j,−(5+72·3^j)) → (3+j,−(5+72·3^(j+1)))`.  All these realized edges concatenate in the *coefficient-state graph* into one infinite descending chain, even though they need not come from one positive orbit.  This argument covers ordinal-valued ranks as well as natural-valued ranks.  It does not rule out grouping the entire odd phase with a later exit, or a rank using actual integer vertices and a separately justified resource.  The formal negative reference specifies finite parity cylinders; it is not asserted to be an infinite positive trajectory.
