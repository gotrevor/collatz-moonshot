# Primitive short-run rational positivity does not bound length

Date: 2026-09-13. This is an all-parameter mathematical proof supported by an
exact rational certificate and independent finite controls. It is **not a new
Lean theorem**. Reproduce with `python3 experiments/short_run_obstruction.py`.
The optional `--json PATH` records every finite probe's q, e, b, a, m, R, all
vertices and slacks, N, D, canonical n0, and admission margin as exact values.

## 1. Statement and construction

The proposed statement in DIRECTION.md is false: **there exists Q=2 such that,
for every length bound M, a primitive word of length greater than M satisfies
all the specified rational-cycle hypotheses**. In fact its joint slack is at
least 8/5 and its total multiplier is at most 243/256, uniformly in length.

Put X=TF, Y=T²F, A=XY, B=XYY, and for every integer k≥0 put

```
v_k = A^k B = (TF T²F)^k (TF T²F T²F).
q = (1,2)^k followed by (1,2,2);   e = (1,...,1).
b = 2k+3,   a = 3k+5,   m = 5k+8.
R_k = (27/32)^k (243/256) ∈ (0,243/256].
```

All gaps, including the last, are positive. Adjacent patterns therefore do
not merge odd runs, including at the cyclic boundary. Every individual odd
and even run has length between 1 and 2.

**Primitivity is about the Boolean word**, with exactly the meaning of
`CollatzMoonshot.FrontB.Primitive` in `FrontB/Powers.lean`: nonempty and unequal
to `wpow u j` for every j≥2. If v_k were such a power, j would divide both its
length m and its odd-letter count a. But 5a−3m=1, so j divides 1, impossible.
This handles arbitrary roots, not merely roots aligned with A/B boundaries.
Lengths 5k+8 are unbounded. The family is not the earlier word-power degeneracy.

## 2. Exact interval certificate and the all-k proof

At an odd-run head use precisely the directive's coordinate z=x+1. For a
block T^q F^e its affine map is

```
f_(q,e)(z) = 3^q / 2^(q+e) * z + 1 - 2^(-e).
f_X(z) = 3z/4 + 1/2;     f_Y(z) = 9z/8 + 1/2.
f_A(z) = 27z/32 + 17/16.
f_B(z) = 243z/256 + 217/128.
```

Word composition is chronological: f_A=f_Y∘f_X and
f_(v_k)=f_B∘f_A^k. The common interval is I=[34/5,434/13].
The two macro maps have positive slope less than one, and their exact images
are

| pattern | image of I | lower joint slacks z−2^q, in chronological order |
|---|---|---|
| A=XY | [34/5,380/13] ⊆ I | 24/5, 8/5 |
| B=XYY | [163/20,434/13] ⊆ I | 24/5, 8/5, 14/5 |

Every internal prefix has positive slope. Evaluating it at the lower input
34/5 therefore proves the displayed lower slack bounds for **all inputs in
I**. Internal vertices need not themselves lie in I; only macro boundaries
use the invariant interval. This distinction is checked in the experiment.

Induction on k shows f_B∘f_A^k maps I into I. Write this affine map as
R_k z+S_k. Since 0<R_k<1, it has the unique rational fixed point
z0=S_k/(1−R_k). The endpoint inequalities

```
(1−R_k)*(34/5) ≤ S_k ≤ (1−R_k)*(434/13)
```

put z0 in I. Following A k times and then B stays in I at each macro
boundary; the internal-prefix certificate gives z_i−2^q_i≥8/5>0 at every
odd-run start, including the two Y starts in B. The final value is z0 by
construction. This proves the rational recurrence, closure, strict positivity,
and uniform slack for **every k**, not just the finite probes.

An independent explicit recurrence is useful for auditing orientation. Let
h=34/5 and t_k=(27/32)^k. Then

```
f_A^k(z) = h + t_k*(z−h),
f_B(h) = 163/20,
z0(k) = [163/20 − (4131/640)*t_k] / [1 − (243/256)*t_k].
```

The experiment checks this expression against the existing integer cascade
and independently checks every cyclic joint identity. The finite certificate
consists of the two macro coefficient identities, positive slopes, interval
endpoints, and internal-prefix slack inequalities; the preceding induction
is what turns those finite facts into an unbounded family.

## 3. The integer information that rejects the entire family

For v_k retain N and D separately from its realizing residue. Direct affine
composition, equivalently the repository's numerator append identity, gives

```
N_A=29,  N_B=421,
D_k = 256*32^k − 243*27^k > 0,
N_k = [9152*32^k − 7047*27^k]/5,
z0(k) = 1 + N_k/D_k.
```

For example N_(A^k)=29*(32^k−27^k)/5, and appending B gives
N_k=243*N_(A^k)+421*32^k. These are integer formulas; the division by 5 is
exact. The integer fixed-point threshold x*=N_k/D_k is not a realizing start.

Let n0(k) be the least representative above 2 of the word's unique residue
class modulo 2^m. The **full** exact canonical formula and recurrence are

```
n0(k) = [−N_k * (3^(3k+5))^(-1)] mod 2^(5k+8),
n0(0) = 249,
n0(k+1) = [(32*n0(k)−29) * 27^(-1)] mod 2^(5k+13).
```

In these formulas the least nonnegative representative already exceeds 2,
as the common prefix below proves. The recurrence follows by prepending A:
27*n+29=32*y, where y must realize v_k modulo 2^(5k+8).

Every word v_k starts with the **same six letters TFTTFT**, whose odd count
is 4 and whose numerator is 119. The corresponding necessary congruence is

```
81*n + 119 ≡ 0 mod 64,  equivalently n ≡ 57 mod 64.
```

Thus every positive realizing start, including n0(k), is at least 57. In
contrast the invariant interval gives

```
N_k/D_k ≤ 434/13−1 = 421/13 < 57,
N_k − D_k*n0(k) ≤ −(320/13)*D_k < 0.
```

Consequently **no member of this family admits any positive integer start
with strict endpoint growth**. The least realizing start already exceeds the
threshold, and larger representatives only decrease N−D*n. This is an
all-k rejection, not an observed absence of finite admissions. It does not
require testing integrality of the auxiliary fixed point (which would be the
wrong condition for a segment with strict growth). A six-letter prefix
congruence plus the rational head threshold suffices.

| k | m | z0 | canonical n0 | N−D*n0 |
|---|---|---|---|---|
| 0 | 8 | 434/13 | 249 | −2816 |
| 1 | 13 | 22150/1631 | 6969 | −11345920 |
| 2 | 18 | 931874/84997 | 144185 | −12254445568 |
| 3 | 23 | 35842966/3605639 | 5452601 | −19660078579712 |

The script also verifies the actual parity trace of each finite n0 and the
identity N−D*n0=2^m*(iterate(n0,m)−n0). It independently compares the modular
inverse formula with bit lifting for k≤8. For every sampled k it checks the
canonical recurrence, all vertices from `block_composition.cascade`, the
closed forms, literal Boolean-word primitivity, and every joint slack.

## 4. Costume check and precise remaining scope

This refutes the proposed universal M_Q **for the rational relaxation**, already
at Q=2 and with R bounded away from 1. It refutes neither Collatz nor
paradoxical finiteness: every member is rejected by an explicit admission
congruence. It does not show the old 2^b−1 exponent optimal and does not
exclude improved real bounds depending on b. The invariant interval even
keeps the entry fixed points uniformly bounded while total length diverges.

This is an architecture obstruction, with no literature-novelty claim and no
new Collatz axiom. A uniform argument for actual segments must use information
beyond the tested rational hypotheses. Here the missing input is exactly
the six-bit prefix congruence relative to the head threshold; in general the
known complete input is canonical admission D*n0<N. Establishing a useful
uniform arithmetic exclusion across arbitrary words remains open. Assuming
bounded length or run count for all actual admitting words would rename the
restricted finiteness target, so it is not supplied as a next lemma.

The assigned bounded architecture/probe objective is complete. Stop for an
altitude decision before undertaking a general prefix-filter or distribution
campaign. No rung 4/5 classification, fixed-b census, constant sharpening,
or Front B transport was attempted; the existing controls were rerun unchanged.
