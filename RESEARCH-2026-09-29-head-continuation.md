# The two-row head peel and its next-frontier obstruction

The two symbolic supply subclasses give an exact first-edge extraction.  They do not yet give a target-free repair.  This note separates the central Q-row calculation from any unit words used to make its inputs available, and proves that a uniform affine *single-Q* repetition of the same head peel is impossible.  It leaves non-affine, multi-row and different-frontier repairs open.

Use `r_u=2u/(3u+1)` for positive odd `u` and `B(r_u)=e_u-e_{T(u)}`.  In the lower family, put

```
n=9223+16320h,  c=3689+6528h,  d=5425+9600h,
m=45((n-7)/64)+5,  a=T(n)=(3n+1)/2,
v=T(5n)=(15n+1)/2=5a-2.
```

The two subprogressions and their supply rows are:

| class | h | x | z | b |
|---|---:|---:|---:|---:|
| 95 | `2+95t` | `3349+124032t` | `785+29070t` | `661+24480t` |
| 79 | `1+79t` | `3005+151680t` | `5635+284400t` | `2425+122400t` |

For every `t>=0`, both rows are legal scalar Q identities:

```
r_x r_z = r_c r_b,
r_(5n) r_c = r_n r_d.
```

Thus the central composition is

```
r_(5n) r_x r_z = r_n r_d r_b.                         (1)
```

All five local auxiliaries `c,d,x,z,b` are below **m**, not just below `n`.  For class 95, `m=29435+1090125t`; for class 79, `m=17960+906525t`.  Comparison of both constants and slopes with the table and the formulas for `c,d` proves every inequality.  This would put their availability below the induction endpoint if a suitable restricted-palette unit-borrowing theorem were supplied.  Under unrestricted semigroup generation, availability is already automatic for each 3-free label `u`: the reduced denominator of `1/r_u=(3u+1)/(2u)` is not divisible by 3, so the Applegate-Lagarias semigroup theorem represents `1/r_u`; multiplying by `r_u` gives a finite positive unit containing `u`.  The two rows do not give a restricted-palette borrowing grammar or directed flow.

## What the composition leaves

The virtual six-step word contains the consecutive odd edges `5n -> v -> T(v)` before four even steps to `m`.  Equation (1) removes the edge from `5n` and installs the genuine first edge from `n` to `a`, but keeps the edge from `v`.  If a supplied balanced certificate for `m` is left untouched, the scalar remainder after cancelling `r_n` is a certificate for `a`, not a second instance of the same lower-family construction.  Indeed `a≡11 (mod 64)` when `h` is even and `a≡43 (mod 64)` when `h` is odd, never `7`.  Moreover `a>n`.

The central boundary change from the two Q rows is exactly

```
Delta = B(r_n)+B(r_d)+B(r_b)-B(r_(5n))-B(r_x)-B(r_z).
```

Against the initial frontier defect `e_(5n)-e_n`, its residual is

```
e_v-e_a + B(r_d)+B(r_b)-B(r_x)-B(r_z).               (2)
```

All variable supports in (2) other than `v` are below `v`, since `x,z,b,d<n`, their odd successors are below `a`, and `a<v`.  The coefficient at `v` is therefore `+1`.  On the *projected central defect*, with fixed virtual-prefix edges and inverse-five factors placed at small vertices, the top vertex moves upward from `5n` to `v>5n`; max-vertex descent fails for that projection.  It is not a statement about the whole executable borrowing state: inserted unit words containing `x,z` remain altered after these moves, can have large vertex support, and need further legal rewrites.  Arbitrary unit insertion cannot be treated as zero boundary merely because its scalar value is one.

The virtual edge also cannot meet the guaranteed actual growing prefix.  The first six actual states are all below `v`.  Since `n≡3 (mod 5)`, one has `v≡3 (mod 5)` but `p=T^6(n)=11674+20655h≡4 (mod 5)`.  An odd shortcut step preserves residue 4 modulo 5, so every state in the consecutive odd run following `p` is 4 modulo 5 and differs from `v`.  This uses only the fixed six-step word and its initial odd run, not a known target trajectory.

One could rank the virtual frontier by the number of its fixed six steps remaining: the first peel changes `5n` to `v`, apparently reducing that count from six to five.  Formula (2) shows the missing obligation precisely.  A second peel would need to replace the still-present `r_v` by the genuine `r_a` while controlling its new auxiliary factors and the borrowed-unit boundary.  The next theorem excludes the most direct affine one-row version of that obligation.

## Complete affine classification of the direct second peel

Let `a` vary without bound on any affine subprogression, and suppose `Q(a),E(a)` are affine rational functions, positive integers for all parameters in that progression, satisfying

```
r_(5a-2) r_(Q(a)) = r_a r_(E(a)).                    (3)
```

Positivity on an unbounded progression gives nonnegative slopes.  A zero slope for either `Q` or `E` is impossible: after clearing denominators, the fixed numerator roots `2/5` and `-1/3` on the left cannot both be matched by the single remaining variable root on the right.  For positive slopes, write `q0,qp` for the zero and denominator roots of `Q/(3Q+1)`, and `e0,ep` for those of `E/(3E+1)`.  Each denominator root lies strictly below its numerator root: `qp<q0`, `ep<e0`.

Clearing denominators in (3) gives the multiset identity

```
{2/5, -1/3, q0, ep} = {0, 1/3, e0, qp}.           (4)
```

The fixed left roots are distinct from the fixed right roots.  Hence `{e0,qp}={2/5,-1/3}` and `{q0,ep}={0,1/3}`.  The assignment `qp=2/5` is impossible because `q0<=1/3`.  Thus `e0=2/5`, `qp=-1/3`, leaving exactly two cases:

| `q0` | `ep` | `Q(a)` | `E(a)` | status |
|---:|---:|---|---|---|
| 0 | 1/3 | `a` | `5a-2` | unchanged pair |
| 1/3 | 0 | `(3a-1)/6` | `(5a-2)/6` | `Q(a)` is never integral |

Both satisfy the rational identity; their leading constants match because both sides tend to `(2/3)^2` as `a` tends to infinity.  For every integer `a`, `3a-1≡-1 (mod 3)`, so the second case is never a legal integer-label Q row.  Thus there is **no nontrivial affine single-Q rule** that directly replaces the virtual `r_v` by the actual `r_a` throughout either supply subclass or any infinite affine subprogression.  This includes affine companion labels with different denominators, since the classification was over rational affine functions before the integer test.  It does not exclude non-affine labels, a higher-arity identity, a different choice of next actual factor, or a rewrite involving even-edge locations.

## A positive cubic escape on a sparse subprogression

The affine Q obstruction is sharp as a one-row obstruction.  A three-factor identity splits the interval from `-(K-3)/9` to `7/2` into three numerator/denominator-root intervals on either side.  For any rational `a>7/2` and suitable positive `K`, define

```
q1=(3a-1)/K,  q2=5(2a-7)/93,
e1=(3a+1)/(K-6),  e2=(2a-7)/21.
```

Direct cancellation, without any trajectory, gives

```
r_(5a-2) r_q1 r_q2
 = [2(5a-2)/(5(3a-1))]
   [2(3a-1)/(9a+K-3)]
   [5(2a-7)/(3(5a-2))]
 = 4(2a-7)/(3(9a+K-3))
 = r_a r_e1 r_e2.                                  (5)
```

Choose **K=64** on class 95, where `a=62795+2325600t`.  The congruences `t≡3 (mod 116)`, `t≡4 (mod 7)`, `t≡14 (mod 31)` make all four new labels positive odd integers.  Their least common solution is `t=16475+25172s`, `s>=0`.  The affine formulas on this progression are:

| label | constant | coefficient of `s` |
|---|---:|---:|
| `n` | 25542881863 | 39026668800 |
| `m` | 17959838810 | 27440626500 |
| `a` | 38314322795 | 58540003200 |
| `v` | 191571613973 | 292700016000 |
| `q1` | 1795983881 | 2744062650 |
| `q2` | 4119819655 | 6294624000 |
| `e1` | 1981775317 | 3027931200 |
| `e2` | 3648983123 | 5575238400 |

Every new label is 3-free because its constant is 3-free and its slope is divisible by 3.  Constants and slopes also prove `0<q1,q2,e1,e2<m=(15a-5)/32` for all `s>=0`.  At `s=0`, the exact data are

```
n=25542881863,  m=17959838810,  a=38314322795,
v=191571613973,
(q1,q2)=(1795983881,4119819655),
(e1,e2)=(1981775317,3648983123).
```

This subclass meets the hard growth residue, rather than the easy step-7 slice.  Since `t≡3 (mod 4)`, `h=2+95t≡3 (mod 4)`.  More sharply,

```
T^6(n)+1 = 4(8081927465+12348281925s).
```

The coefficient of `s` in parentheses is odd.  Therefore, for every `j>=2`, one residue of `s mod 2^(j-2)` makes `T^6(n)+1` divisible by `2^j`.  The fixed six steps and the next `j` odd steps all rise above `n`.  At `s=0`, the odd run has length exactly two; at `s=1`, length three.  The earlier K=32 progression `t=4540+5642s` instead has even `t`, hence even `h` and descent at step 7.  It remains only an easy-prefix control.

Equation (5) is a *new variable cubic*, not the fixed C5 rule of the restricted palette.  It is a positive odd-factor scalar identity, but the current restricted replay checker has no rule admitting it.  Under unrestricted Applegate-Lagarias generation, both 3-free inputs have positive unit supplies; this settles their scalar availability, not the directed flow.

After (5), the projected central residual (2) becomes

```
e_(16m)-e_(T(a)) + B(r_d)+B(r_b)+B(r_e1)+B(r_e2)
                  - B(r_x)-B(r_z)-B(r_q1)-B(r_q2).  (6)
```

Here `T(v)=16m`: the virtual edge has reached the beginning of the four even steps down to the supplied endpoint.  The actual frontier is `T(a)`, its second odd successor.  The virtual vertex has grown again (`16m>v`), and the low auxiliary boundary terms accumulate.  A rank based solely on largest numerical defect vertex therefore still fails.  A possible structured rank would count remaining virtual-prefix edges, but it must also control the complete lower boundary and the arbitrary inserted-unit words before it is a well-founded full-state measure.  The cubic establishes a second local peel on one sparse class, not a self-similar full repair.

## Finite controls and scope

`experiments/repair_family.py lower-composite {class95,class79} t` command checks both Q equations and (1) by exact integer cross multiplication, and emits the signed central boundary vector without reading the trajectory of `n`.  `second-frontier-pairs {class95,class79} t --ceiling n` enumerates every positive odd pair `q,e<n` for (3).  It uses the unique candidate

```
e = (5a-2)q(3a+1) / [5a(3a-1)-6(2a-1)q].
```

At `t=0`, both complete scans are empty even before requiring 3-free labels: class 95 has `(n,m,a,v)=(41863,29435,62795,313973)`, class 79 has `(25543,17960,38315,191573)`.  These finite controls refute a proposed one-row rule with both auxiliaries below `n` *at those base points*.  The affine classification is the uniform Q result, and the cubic exhibits its higher-arity escape.  The additional `second-frontier-cubic s` command defaults to K64 and checks the exact rational identity, legal-label conditions and odd-run length on the hard CRT class; `--variant easy32` retains the old control.  The persistent subprocess tests run through `experiments/repair_family.py test`.

The next viable rank proposal needs an explicit state including the virtual frontier, the actual frontier, and the borrowed-unit boundary.  It must give a legal block after the cubic whose entire state decreases, despite possible label growth.  A rank on supplier labels alone addresses availability, while a rank on the central maximum vertex already fails at the first peel.  Equations (1) and (5) do not supply that block.
