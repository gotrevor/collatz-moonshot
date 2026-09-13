# Campaign B, architecture lap 1: a cyclic potential contracts arbitrary block count

## Architecture lap 2 update: Campaign B proved

The historical lap-1 proposal below has now been proved and connected to actual
segments. `FrontA/FixedBlocks.lean` proves
`acyclicParadoxical_length_lt_of_oddRunCount` with the explicit bound

```
L(b) = 4*((2^b-1)*(b+53342))^2+b.
```

The factor 4 replaces the proposed factor 2; this small loss permits a purely
natural-number binary-length proof. There is no remaining arithmetic hypothesis,
word bridge, fixed-point construction, or uniform-bound proof obligation for
Campaign B. The theorem concerns all lengths and starts, not only the census.
See `HANDOFF-2026-09-13-fixed-block-bound.md` for exact verification and the
completion decision. The lap-1 text below is retained as the original derivation
and audit, with its former unformalized boundaries now superseded.

The proof avoids the maximum-product construction. For a positive rational
cycle `z_next=r*z+s`, with `s<1` and total multiplier `R=1-δ` in `(0,1)`, suppose
every `z≥b/δ`. Put `c=δ/b`. Then

```
(1-c)*z_next < r*z,
(1-c)^b < R,                 after multiplying and cancelling all z,
R = 1-b*c ≤ (1-c)^b,        by Bernoulli.
```

Thus some vertex has `z<b/δ`. For a nonempty odd run,
`r+1/2≤2^q` and `z≥2^q≥2`; hence `z_next<2^q*z≤z^2`.
Starting at that small vertex gives `z_j<(b/δ)^(2^j)`, and multiplying all
`2^q_j≤z_j` yields exactly the original composition inequality
`2^a<(b/δ)^(2^b-1)`. Finite reindexing preserves the exponent sum. The original
length inequality `2^m<2^b*3^a` follows from the existing multiplier-lower lemma.
All of these statements, including the rational cycle's construction above the
actual integer path, are now kernel-checked in `FrontA/BlockCycle.lean`.

For the final feedback let `t=Nat.log 2 a`, `C=2^b-1`, and
`H=C*(b+53342)`. The existing polynomial measure in both regimes gives
`2^m≤2^(52906+436*(t+1))*D`. Composition implies
`a<C*(b+52906+436*(t+1))≤H*(t+1)`. For `t≥4`, elementary induction gives
`(t+1)^2≤2*2^t≤2a`; squaring and cancelling positive a yields `a<2H^2`.
For `t<4`, `a<16` gives the same bound directly. Therefore
`m<b+2a<4H^2+b`. This is `FrontA/BlockLength.lean`.

The final module counts maximal odd runs by true-to-false transitions with a
false sentinel at the end of the *word*. This sentinel adds no trajectory step.
It extracts exactly that many blocks (allowing zero trailing even steps), proves
every actual head identity by trace splitting, and applies the cascade bound.
The bound is monotone, so an upper bound on the run count suffices, including
`b=0` vacuously. Kernel controls include the terminal-odd 7@8 witness, 9@8,
and the shared-trunk run counts 13 and 11 for 2305 and 2313.

The updated exact probe checks the new small-vertex and squaring mechanism on
all its prior controls and on **449,400** complete exponent tuples at
`(b,m,a)=(4,27,17),(5,27,17)`, including **134,456** rational-positivity survivors.
The previous 46-step complete scans are historical lap-1 evidence; they were
not repeated in lap 2. The preimage remainders and negative controls remain.

**Historical lap 1 — running+advancing.** A new composition mechanism survives: positivity at every
block start, applied to the rational affine fixed point of the whole word, gives

```
2^a < (b/δ)^(2^b-1),             2^m < 2^b 3^a,             (C)
δ = (2^m-3^a)/2^m.
```

This is a uniform inequality in the exponent tuple, not a renamed bounded-length
target. The existing polynomial two-log measure then gives the proposed explicit
bound `L(b) = 2*((2^b-1)*(b+53342))^2+b`. The complete mathematical derivation is
below; **the segment-to-(C) bridge and L(b) theorem are not yet Lean theorems**.
`FrontA/BlockComposition.lean` kernel-checks the arbitrary integer cascade, prefix
composition, conjugation, fixed-point domination, unit-potential cut, one-step
growth, arbitrary-length mass contraction, and multiplier lower bound separately.
Architecture lap 2 should scrutinize and connect the finite cyclic-product bridge.

No global Collatz assumption, no uniform bounded-block theorem, no induction on
the campaign target, and no new separation hypothesis enters the argument.
The rational fixed point below is an auxiliary affine construction, **not** an
assertion that the word realizes an integer cycle.

## 1. Arbitrary-block integer cascade, keeping all remainders

Use zero-based blocks `T^q_i F^e_i`, `0≤i<b`. All `q_i≥1`; `e_i≥1` for `i<b-1`,
and `e_(b-1)≥0`. Let `x_0=n`, `x_b=y`, and `x_i` be the actual block starts.
Set `a=Σq_i`, `m=Σ(q_i+e_i)`, `D=2^m-3^a>0`. Each head identity is

```
2^(q_i+e_i) x_(i+1) + 2^q_i = 3^q_i (x_i+1).
```

`headBlock_scale` supplies positive integers `w_i` with

```
x_i+1 = 2^q_i w_i,
3^q_i w_i + 2^e_i = 2^(e_i+q_(i+1)) w_(i+1) + 1    (i<b-1),
3^q_(b-1) w_(b-1) = 2^e_(b-1) y + 1.
```

These are now packaged for arbitrary b in `blockCascade_of_identities`; it does
not require the positivity of run lengths just to obtain the identities. Define

```
P_0=H_0=1, T_0=0,
P_(i+1)=3^q_i P_i,
H_(i+1)=2^(e_i+q_(i+1)) H_i,
T_(i+1)=3^q_i T_i + H_i(2^e_i-1).
```

The exact inductive invariant is `P_i w_0 = H_i w_i - T_i`.
`blockCascade_compose` kernel-checks its composition step. In particular

```
P_i = 3^(q_0+...+q_(i-1)),
H_i = 2^(e_0+...+e_(i-1)+q_1+...+q_i),
U = 3^q_(b-1) T_(b-1) - H_(b-1),
2^(m-q_0)y = 3^a w_0 + U,
n < y  <=>  D w_0 ≤ U.                                  (I)
```

The last equivalence uses the integer gain `y≥n+1=2^q_0 w_0`. If using only
`y>n` in a real relaxation, one loses a whole `2^(m-q_0)` from this sharp upper
bound. The equivalent original numerator identity is
`N = 2^q_0 U + 3^a`, obtained from `2^m y=3^a n+N`.

Every positivity leaf is

```
D (H_i-T_i) ≤ P_i U,                    0≤i<b.           (PL)
```

These jointly say that there is a real `w_0` satisfying the prefix-scale
positivity constraints and (I). They discard integrality, but retain **every**
prefix correction `T_i`. A stronger necessary lower bound is the nested ceiling

```
l_(b-1)=1,
l_i=max(1, ceil((2^(e_i+q_(i+1)) l_(i+1)-2^e_i+1)/3^q_i)).
```

Admission implies `D l_0≤U`. These ceilings are lower bounds, not necessarily
attained integer solutions of the cascade: intermediate congruences can fail.
Some historical probe docstrings call them the "minimum over integer triples";
that wording must not be imported as a theorem. Actual admission still uses the
canonical parity residue (and the endpoint divisibility).

## 2. Exactly what the completed low-block contractions consume

For two blocks `(q_0,e_0,q_1,e_1)=(b,c,d,e)` in the old notation:

```
U=3^d(2^c-1)-2^(c+d),
w_0≥1,       3^b w_0≥2^(c+d)-2^c+1,       D w_0≤U.
```

`near_critical_containment` obtains the window and the two scale inequalities
`D 2^d<2^m`, `D 2^(b+d)≤2^m 3^d`. The proved `sep_two_three` gives
`3^(3a)≤D^3 2^a`; `bd_reduction` contracts to `a≤5`. Only the two residual
tuples `(2,3,3,0)` and `(3,3,2,0)` then need exact residue equations. Neither the
real tail constraint alone nor positivity alone supplies the literal exclusion.

For three blocks `(b,c,d,e,f,g)`, the recursion gives exactly

```
T_2=2^(c+d+e)-2^(c+d)+3^d(2^c-1), H_2=2^(c+d+e+f),
U=3^f T_2-H_2.
```

The three PL inequalities are precisely the negations of
`threeBlock_gap_of_w1`, `_of_w2`, and `_of_real`. The compiled final proof first
weakens `T_2` to `2^c(2^(d+e)+3^d)`, yielding `threeBlock_relax_W/V/A`.
At deficit scale `2^m≤2^t D`, their feedback yields `a≤6t+5`
(`threeBlock_scaled_k_bound`, using `3^5≤2^8`). The polynomial Rhin-lite measure
bootstraps an explicit range, then two fixed power brackets contract to the
finite exponent census. Nested ceilings and exact canonical residues settle the
exceptional lengths 5,16,27, leaving length 8.

Thus the **final** three-block finiteness proof uses all three positivity leaves
and the polynomial measure; it does not need a new nested-ceiling inequality to
make the exponent range finite. Ceiling rounding sharpens the residual finite
search. Historical comments claiming "not by a linear form in logarithms" are
superseded by the actual final proof. The two-block merge reductions are useful
pruning but are not assumptions of (C); merging arbitrary subcritical pieces
cannot reuse the two-block exclusion as a uniform theorem.

## 3. From a segment to a rational fixed-point envelope

Conjugate to `u_i=x_i+1`. Put

```
r_i=3^q_i / 2^(q_i+e_i) > 0,
s_i=1-2^(-e_i) ∈ [0,1),
u_(i+1)=r_i u_i+s_i,             u_i≥2^q_i.
```

`headBlock_conjugate` proves the coordinate change. Composition gives
`u_b=R u_0+S`, where `R=∏r_i=1-δ<1` and S retains all additive terms.
Define `z_0=S/δ` and propagate the same block maps to get `z_i`.
Then `z_b=z_0`; furthermore `u_b>u_0` implies `z_0>u_0`.
Every prefix has positive slope, so `z_i>u_i≥2^q_i` at every block start
(`affineFixedPoint_dominates` proves the comparison at a given prefix).

It is enough for the next step to assume the weaker **rational positivity**
condition `z_i≥2^q_i` at every vertex. This is deliberately weaker than PL,
and much weaker than an actually admitting word. In the exact cascade its test is

```
D(H_i-T_i) ≤ P_i (U+2^(m-q_0))          for every i.       (FP)
```

Here `w_0*=z_0/2^q_0=(U+2^(m-q_0))/D`. All finite probes below test (C) on
**every FP survivor**, not just the empty b=4,5 admitting populations.

## 4. The decisive cyclic composition inequality: mathematical proof

Index cyclically modulo b. Let `M_i` be the maximum of the products of
`0,1,...,b-1` consecutive multipliers ending at vertex i (empty product = 1).
The full product R is less than one, so including a full circuit never raises
this maximum. Directly shifting the finite products proves

```
M_i≥1,          M_(i+1)=max(1, r_i M_i).                 (MP)
```

At least one M_i equals one. Otherwise the multiplier branch is selected at
every vertex; multiplication of (MP) gives `∏M_i=R∏M_i`, impossible since
`∏M_i>0` and `R<1`. This step is kernel-checked as `blockPotential_has_unit`.
This is the useful cut: it depends only on the block multipliers. It is **not**
claimed to be the actual orbit minimum or to preserve admission of a rotated
integer word.

Unroll the affine fixed orbit once, ending at vertex i:

```
δ z_i = Σ_(j=0)^(b-1) s_(i-j-1) ∏_(h=1)^j r_(i-h) < b M_i.
```

Each product is positive and at most M_i, and each s is strictly below one;
b≥1 makes the sum inequality strict. Combining with FP gives
`2^q_i < K M_i`, where `K=b/δ>1`. Also `r_i≤2^q_i`, using only `3≤4` and
`e_i≥0`. Consequently

```
M_(i+1) ≤ K M_i^2.                                     (G)
```

`blockMultiplier_le_two_pow` and `blockPotential_step` prove this step. Start at
the vertex `M_l=1` and follow the cycle once. Ordinary finite induction gives

```
M_(l+j) ≤ K^(2^j-1),       2^q_(l+j) < K^(2^j),
2^a < K^(1+2+...+2^(b-1)) = K^(2^b-1).
```

The arbitrary-length induction and strict product bound are kernel-checked as
`blockPotential_mass_bound`. No run is assumed short in this induction; its
input is the local growth inequality (G), and its start is supplied by MP.
Equivalently the result is the exact integer inequality

```
2^a D^(2^b-1) < (b 2^m)^(2^b-1).                        (C1)
```

Length also contracts: `z_(i+1)≥2` and `s_i<1` imply
`r_i z_i=z_(i+1)-s_i>z_(i+1)/2`. Multiplying and cancelling the positive z
product gives `R>2^(-b)`. This is `affineCycle_multiplier_lower`, giving

```
2^m < 2^b 3^a < 2^(b+2a),       hence m<b+2a.           (C2)
```

**Scope:** C1–C2 hold for every FP exponent tuple, including tuples with no
integer realizing cycle or paradoxical segment. They also apply to a segment
with endpoint equality, since domination then becomes equality. They use all
joint positivity constraints, but do not use ceiling rounding or exact residue
selection. They do not imply that the lengths of segments with unbounded b are
bounded. The constants intentionally sacrifice the sharp rung-3 slope.

## 5. Existing separation closes the numerical feedback

This is a mathematical deduction; it is not yet a Lean theorem of this lap.
Set `C=2^b-1`, `C0=2*396^6000*6^436≤2^52905` (the latter certificate already
exists as `rhinLite_loose_constant_le_two_pow`). In the near-critical window,
`rhinLite_nat_measure_loose` says `3^a≤D C0 a^436`. Since `2^m<2*3^a`,

```
δ ≥ 1/(2 C0 a^436) ≥ 2^(-52906) a^(-436).
```

Outside that window, `δ≥1/2` implies the same loose bound for `a≥1`.
Taking base-two logarithms in C1, with `log₂ b≤b`, yields

```
a < C (b+52906+436 log₂ a).                              (F)
```

For `a≥16`, the elementary inequality `log₂ a≤sqrt(a)` and `sqrt(a)≥1` imply
`sqrt(a)<C(b+53342)`. The smaller a also satisfy the resulting bound for b≥1.
Therefore an explicit proposed bound is

```
A(b) = ((2^b-1)*(b+53342))^2,
L(b) = 2 A(b)+b.                                        (L)
```

C2 gives `m<L(b)` for exactly b blocks. L is increasing, so it also bounds at
most b blocks. `L(0)=0` is harmless: an odd-start positive-length segment has at
least one odd run. The asymptotic size of this deliberately loose bound is
`O(4^b (b+53342)^2)`. It provides no small-rung classification.

## 6. Exact controls and their limits

`experiments/block_composition.py` checks the cascade on 4,000 actual odd-start
segments (starts 3..201, lengths 1..40), checks equality with all three existing
rung-3 positivity/ceiling formulas at every subcritical tuple through m=18,
and checks the cyclic mechanism on all 320 reported admitting starts through
start 5000 at the six A1 table lengths. This retains A2 as settled input;
it adds the block decomposition and potential checks, not a new excursion audit.

The nonvacuous exponent probes are complete at each displayed `(b,m,a)`:

| b | m | a | tuples | FP | all PL | ceiling | actual admitting |
|---|---|---|---|---|---|---|---|
| 1 | 8 | 5 | 1 | 0 | 0 | 0 | 0 |
| 2 | 8 | 5 | 12 | 12 | 3 | 2 | 0 |
| 3 | 8 | 5 | 18 | 18 | 17 | 17 | 4 |
| 4 | 16 | 10 | 1680 | 687 | 390 | 194 | 0 |
| 5 | 16 | 10 | 1890 | 1344 | 1017 | 809 | 0 |
| 4 | 27 | 17 | 67200 | 8581 | 5052 | 2811 | 0 |
| 5 | 27 | 17 | 382200 | 125875 | 95678 | 74503 | 0 |
| 4 | 46 | 29 | 2227680 | 1752 | 1137 | 182 | 0 |
| 5 | 46 | 29 | 48730500 | 678142 | 441530 | 159101 | 0 |

Every FP survivor passes each cyclic sum identity, MP, the unit cut, each
inductive potential bound, C1 and C2, with exact rational/integer arithmetic.
This is stronger finite evidence than testing only realized segments, but the
uniform assertion rests on the derivation, not the scan. No all-length b=4,5
exclusion is inferred from these finite probes.

Small positivity survivors such as
`q=(1,2,3,4), e=(1,1,1,3)` at b=4, and
`q=(1,1,1,3,4), e=(1,1,1,1,2)` at b=5 show why using just the existing
literal exclusions as a block-merging induction would be inadequate.

A negative control verifies that the joint hypotheses carry real force. For
b=2,3,4,5, take `Q=32b`, `q=(1,...,1,Q)` and `e=(1,...,1,2Q,0)` (b-2 initial
unit gaps). The rational fixed point satisfies every run-start bound except the
last, and **violates C1**. These are not counterexamples to the target: they
refute a proposed proof that discards even that one joint's positivity.

For the shared trunk, the complete retained block data are:

```
n=2305: q=(1,1,1,1,1,1,3,4,1,3,2,6,4),
        e=(1,1,1,2,2,1,1,1,2,1,1,2,1),   b=13, N_d=7207;
n=2313: q=(1,3,1,1,3,4,1,3,2,6,4),
        e=(1,1,1,5,1,1,2,1,1,2,1),       b=11, N_d=1375.
```

Both cut after `(k,j)=(14,6)` at 103 and share the suffix to 2308.
`D*103-3^6*N_c=21560735825920`; the retained `2^32*N_d` is respectively
30953829302272 and 5905580032000. The exact criterion still accepts only 2305.
The new composition inequality is only a necessary envelope; it never
substitutes a trunk-only admission predicate. The differing b also prevents
treating the pair as identical inputs to a block-count theorem.

## 7. Next decision and evidence boundary

Lap 1 has produced a new inequality and mechanism; the two-lap no-progress
stopping rule has not fired. The next highest-value attack is to kernel-connect
the finite cyclic products: define M_i from a block word, prove MP and the
cyclic affine sum identity, transport the run sum through the unit cut, and use
the already-proved mass contraction. This is a finite algebra/combinatorics
obligation, independent of any Collatz convergence assertion or new Diophantine
estimate. Then connect the numerical separation bound and L(b).

The full theorem should quantify actual words/runs, and should explicitly derive
the head identities from `traceWord` via `segment_identity_of_word`. Do not
silently assume an integral rotated word or an integral fixed point. No active
obligation has been removed or hidden behind an axiom or a `sorry`.
