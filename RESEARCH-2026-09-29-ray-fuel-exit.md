# Binary fuel at the coefficient ray: exit and two exact refills

This is a local paired-shortcut calculation.  Start with positive odd `v`, `e,j≥0`, `m=72·3^j`, and

```
A=m·2^e v−5,       B=2^e v+1,       A+5=m(B−1).
```

The integer pair is **not** assumed to occur in the original hard family.  The existing hard-family CRT lift realizes arbitrary finite *old-ray* prefixes, but supplies no general return script after their first exit.

## Exact fuel consumption and first exit

Compare with the 2-adic reference pair `(-5,1)`.  Its target word repeats `110` and its auxiliary word repeats `10`.  If `e=6q+r`, `0≤r<6`, exactly `q` full six-step blocks are forced.  At those block boundaries,

```
A_{6i}+5=72·3^(j+i)·2^(e−6i)·27^i v,
B_{6i}−1=2^(e−6i)·27^i v,      0≤i≤q.
```

Both vertices follow the reference parities for exactly the first `e` paired choices.  At time `e`, the auxiliary parity flips; the target follows its reference for another three choices and first flips at time `e+3`.  Put `C=3^ceil(e/2)v` and let `α_i` cycle `(-5,-7,-10)` and `β_i` alternate `(1,2)`.  With `a_i=i−floor(i/3)`, the exact values at first exit are

```
A_e=α_e+72·3^(j+a_e)v,
B_e=β_e+C.
```

Since `C` is odd, `B_e` has parity opposite `β_e`.  Its actual next step is

```
B_{e+1}=(C+1)/2       if e is even,
B_{e+1}=(3C+7)/2      if e is odd.
```

The renewed distance from the *next reference auxiliary* is `(C−3)/2` for even `e`, or `(3C+5)/2` for odd `e`.  Each can have arbitrarily large 2-adic valuation as `v` ranges over suitable positive odd residue classes.  This is **one-sided** renewed precision: the target has only two reference-parity bits left at that point.

There is no immediate reset to the same fixed-offset ray at time `e+3`.  If `e mod 3` is `0` or `1`, then `A_{e+3}+5` is odd and cannot equal `(72·3^k)(B_{e+3}−1)`.  If `e=6q+2` or `6q+5`, put `M=3^(j+q+5)`; then `A_{e+3}+5=MC−5`.  For the four actual two-bit auxiliary branches after its exit step, `8(B_{e+3}−1)=DC+E` with

| `e mod 6` | two-bit words `00,01,10,11`: `(D,E)` |
|---:|---|
| 2 | `(1,−7), (3,−1), (3,−3), (9,11)` |
| 5 | `(3,−1), (9,17), (9,15), (27,65)` |

Every admitted branch has `B_{e+3}−1>0`.  Its ratio `8(MC−5)/(DC+E)` lies strictly between consecutive multipliers `8·3^k`, so cannot equal any `72·3^k`.  For negative `E` it is between `8M/D` and `24M/D`; for positive `E` it is between `(8M/D)/3` and `8M/D`.  The lower bound `C≥3` suffices except the `(1,−7)` branch, whose admitted `C≡7 (mod 8)` is a multiple of three and hence `C≥15`.  This excludes only the **first joint deviation**; a later branch can return.

For a second precision check, set `δA=A_{e+4}−α_{e+4}`, `δB=B_{e+4}−β_{e+4}`.  The four-bit auxiliary branch gives `δA=(C_A v+c)/2`, `δB=(D v+F)/16`, with `c=9,13,−19` according to `e mod 3`, `C_A=3^ell D`, and `ell≥0`.  Its `(h,F)` table, where `D=3^(ceil(e/2)+h)`, is

| `C mod 16` | even `e`: word, `h`, `F` | odd `e`: word, `h`, `F` |
|---:|---|---|
| 1 | `0101,2,7` | `1100,2,−9` |
| 3 | `0010,1,−9` | `1000,1,−25` |
| 5 | `0110,2,3` | `1110,3,41` |
| 7 | `0001,1,−5` | `1011,3,51` |
| 9 | `0100,1,−11` | `1101,3,45` |
| 11 | `0011,2,13` | `1001,2,−3` |
| 13 | `0111,3,49` | `1111,4,195` |
| 15 | `0000,0,−15` | `1010,2,−7` |

Here `ell=j+q+4−h` for residues `0,1,3`, `ell=j+q+5−h` for residue `4`, and `ell=j+q+6−h` for residues `2,5`.  Thus

```
2δA−16·3^ell δB = Δ := c−3^ell F.
```

In every table branch `Δ≠0`: the only plausible positive matches are `c=9,F=3,ell=1` and `c=13,F=13,ell=0`, but their rows have respectively `ell≥2` and `ell≥3`; `c=−19` cannot equal `3^ell F` for any listed negative `F`.  If both deviations have valuation at least `k`, then `k≤v₂(Δ)−1`.  This bounds **simultaneous distance to the old reference at time `e+4` for fixed `e,j`**, not a full-state rank.  The following six-step returns show why a bound at this one instant is not a replenishment prohibition.

## Two actual six-step refills from zero old fuel

At `j=0,e=0`, take `v=7+64t`, `t≥0`.  The actual words are target `110010`, auxiliary `000101`, giving

```
(A,B)=(499+4608t, 8+64t)
  →^6 (211+1944t, 2+9t),
A_6+5=216(B_6−1),       B_6−1=9t+1.
```

The old `B−1=7+64t` is odd, while choosing `t_k=(64^k−1)/9` gives `B_6−1=64^k`, arbitrarily high new fuel.  Equivalently `t_0=0`, `t_{k+1}=64t_k+7`.  This is a genuine multiplier change `72→216`, witnessed by positive actual vertices; the target **contracts** from `499+4608t` to `211+1944t` during this return.

At `j=1,e=0`, take `v=45+64t`.  The words are target `110010`, auxiliary `011100`, yielding

```
(A,B)=(9715+13824t, 46+64t)
  →^6 (4099+5832t, 20+27t),
A_6+5=216(B_6−1),       B_6−1=19+27t.
```

Because `27` is odd, each congruence `19+27t≡0 (mod 2^k)` has a positive solution `t`.  Thus this **same-signature** return also replenishes arbitrarily high fuel from old `B−1=45+64t` odd.  Its target contracts strictly as well.  These two branches disprove any proposed rank that simply decrements binary fuel on every completed local return.  They do not refute a rank that charges the target's numerical contraction, and they do not prove a covering return for all outgoing ray states or the original hard-family orbit.


## Whole-phase accounting and coverage verdict

The [hard-family lifting audit](RESEARCH-2026-09-29-ray-refill-hard-lift.md)
proves on paper that the first refill occurs before target descent in
infinitely many actual hard-family starts, with any prescribed new fuel.
This is more than a generic positive-pair control.  The second return is
a separate local rule; no universal iteration of either rule is asserted.

Suppose the first refill gives exactly `6q` new bits.  After its next `q`
normal ray blocks, with pre-refill target `A0`, the endpoint is

```
Aend+5 = (81/64)^q * (27*(A0+5)+216)/64.
```

For `q≥4`, `Aend>A0`: already `27*81^4 > 64^5`.
Thus the immediate target shrinkage does not bound the growth during an
arbitrarily refilled following phase.  This refutes that particular size
accounting, not every amortized rank.  The auxiliary still strictly
decreases during each of the two returns and each ordinary six-step ray
block.  It would be a useful natural-number rank **if** those blocks
covered an invariant positive state class with a valid terminal rule.

The known three block families fail that coverage test explicitly.
For the first return, take `v=7+4096t`.  Its successor is at multiplier
216 with `B'-1=1+576t`, odd and congruent to 1 modulo 64.  It has no
full ordinary ray block (zero fuel), cannot use the multiplier-72
return, and misses the multiplier-216 return's residue 45 modulo 64.
The hard-family CRT argument realizes this residue class infinitely
often before descent.  Hence these rules do not cover their own
successors, including in the intended hard domain.  This is a verdict
about the specified rules, not a claim that no later or different
return is possible.

The bounded pass therefore supplies two genuine contracting return
rules and a precise fuel-refill obstruction, but **no reusable complete
induction**.  The test did not clear the research gate.  Move the main
mechanism search away from extending this particular rule list unless
a coverage argument appears; further isolated return scripts do not
by themselves improve the induction.  Variable-depth repair in general
remains open, as do the independent pairwise and operator inputs.

## Formal and executable scope

[RayRefill.lean](CollatzMoonshot/Obstructions/RayRefill.lean) proves both
six-step positive return families, their exact before/after relations,
and strict contraction of both vertices.  It also proves
`9*refillT k+1=64^k` and the actual first-return endpoints
`B'-1=64^k`, `A'+5=216*64^k`, while the old `B-1` is odd.
Thus arbitrarily high **joint** fresh precision is proved through
actual shortcut iterates.  Frozen CI consumers preserve the definitions
and theorem statements.

The original-hard-family lifting, first-deviation determinant bound,
following-phase comparison, and coverage argument above remain paper
results.  They are not claimed as Lean theorems.  The local formal
result is not a formal universal no-go for adaptive ranks.

The incumbent CLI now has `q1-ray-exit j e v`, which records the exact
first deviations and inherited rational coefficients through `e+4`
steps, and `q1-ray-refill K`, which constructs an actual hard-family
start with exact fresh fuel `K`, verifies its pre-descent prefix, then
follows the entire new shadow phase and both first deviations.  The
last complete six-step checkpoint records the remaining fuel and
compares both vertices with their pre-refill values.  `K=24` checks
the target regrowth and continued auxiliary shrinkage.

The optional `--odd-part-mod64 R` constrains the refilled odd part using
the same CRT constructor.  With `K=0`, `R=1` exhibits the coverage failure;
`R=45` admits the second return and the exact replay descends at original
target step 29.  These are executable controls for the two paper classes.

`./experiments/repair_family.py test` passes all 37 subprocess tests;
the root Lean build and CI declaration consumers pass.  The bounded
formalization handoff is [here](HANDOFF-2026-09-29-ray-refill.md).
