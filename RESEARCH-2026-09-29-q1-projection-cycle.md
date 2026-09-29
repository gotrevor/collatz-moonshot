# Spurious paths in the multiplier-offset projection

This tests the projected state `A+1=m(B−1)+d` after the odd `q1`
phase exit.  A state `(m,d)` records an affine relation between two
*actual* shortcut frontiers; it does not record their integer values or
the parameter residue.  The question is whether such states alone can
carry a well-founded rank under every locally admitted synchronous
step.  The answer is no, even when every finite path is required to be
realizable by positive hard-family parameters.

## Exact projected update

For an odd target step, `A'+1=3(A+1)/2`; for an even step,
`A'+1=((A+1)+1)/2`.  For an odd auxiliary step,
`B'−1=(3(B−1)+2)/2`; for an even step,
`B'−1=((B−1)−1)/2`.  Substitution into `A+1=m(B−1)+d` gives the
closed rational update table:

| target, auxiliary parity | `m'` | `d'` |
|---|---:|---:|
| odd, odd | `m` | `(3d−2m)/2` |
| odd, even | `3m` | `(3d+3m)/2` |
| even, odd | `m/3` | `(d+1−2m/3)/2` |
| even, even | `m` | `(d+1+m)/2` |

At an odd-`L` exit with `L=2r+3`, the starting projection is
`m=8·3^r`, `d=−20·3^r`.  The two-dimensional rational class is
algebraically closed, but closure alone does not give a rank.

## A hard pre-descent projected ray

The strongest control uses a 2-adic reference, **not** an actual positive
start.  Set `r=0`, so `L=3`, and take `u_* = −1/9`, an odd 2-adic integer.
Its formal exit pair is

\[
A_*=36u_*-1=-5,\qquad B_*=(9u_*+7)/2=3.
\]

The target repeats the negative shortcut cycle
`−5→−7→−10→−5` (parities `odd,odd,even`), while the auxiliary follows
`3→5→8→4→2→1→2→1→...`.  At synchronized step 9 they are `(−5,1)`.
Their first nine odd-step counts are `6` and `4`, so the projected
state is `(m,d)=(8·3^(6−4),−4)=(72,−4)`.

Thereafter a six-step block has target word `OOEOOE` and auxiliary
word `OEOEOE`.  Its exact branch formulas are

\[
T^6(A)={81A+85\over64},\qquad
T^6(B)={27B+37\over64}.
\]

The first fixes `−5` and the second fixes `1`.  Since
`A+5=m(B−1)` at `(m,d)=(m,−4)`, the block gives
`A'+5=3m(B'−1)`.  Thus the projected states at steps
`9,15,21,...` follow the infinite ray

\[
(m,d)=(72\cdot3^j,-4),\qquad j=0,1,2,\ldots.
\]

Every finite prefix of this ray is realized by **positive actual
hard-family parameters**.  For exact `L=3`, write `s=7+8t`; then
`u(t)=u_0+2Et` with odd `E=12348281925`.  It visits every odd residue
modulo every power of two.  For any finite horizon, choose arbitrarily
large positive `t` with `u(t)≡−1/9` to enough binary digits.  The
actual target and auxiliary have the reference paired parity words to
that horizon and therefore the same projected states.

These positive lifts are not made easy by an early target descent.
Their original target is `n=(1024u−137)/81`.  Its fixed first six
steps exceed `n`, and steps 6, 7, 8 are respectively
`16u−1`, `24u−1`, `36u−1`, all above `n`.  During the reference target
word, for every admitted `j`,

\[
A_{3j}+5=(9/8)^j\,4(9u+1),
\]

and the two intermediate odd steps increase it.  The least target
value in the entire admitted suffix is `A_0=36u−1>n`.  The auxiliary
suffix has maximum at its second step,
`B_2=(81u+73)/8<n` for `u≥5`, since the inequality is exactly
`1631u>7009`.  The initial auxiliary prefix is smaller still.  Thus
for each prescribed horizon one can choose a positive hard-family
parameter with **all target prefixes above `n` and all auxiliary
prefixes below `n`** throughout that horizon.

No one positive target follows this infinite paired path.  Repeating
`OOE` forever would require, from step 9,
`T^{3j}(x)+5=(9/8)^j(x+5)` to be an integer for all `j`, hence
`8^j | (x+5)` for all `j` and `x=−5`.  This is impossible for a
positive target.  The ray is spurious because each longer prefix uses
a different positive parameter.

The finite fuel discarded by `(m,d)` is visible explicitly.  Put
`J=v₂(9u+1)` for a positive lift.  Along the admitted prefix,

\[
A_9+5={729(9u+1)\over128},\qquad
B_9-1={81(9u+1)\over1024}.
\]

At each six-step ray block, both differences lose six powers of two;
in particular `v₂(B_{9+6j}−1)=J−10−6j` while the block is admitted.
Every actual positive lift has finite `J` and eventually exits this
ray.  The formal reference has `J=∞`.  A rank that remembers this
remaining precision can decrease on the ray, but its behavior after
the exit is a separate obligation.

Therefore **no well-founded rank of `(m,d)` can strictly decrease on
every locally positive-admitted projected block while the actual target
has not descended**.  The ray supplies an infinite chain of such
blocks.  A parameter-aware or full-frontier rank could still work:
it can record the finite 2-adic precision spent by each approximant,
which `(m,d)` has forgotten.

## Formal result and evidence boundary

[CoefficientRay.lean](CollatzMoonshot/Obstructions/CoefficientRay.lean)
proves the positive local block identities and the well-founded rank
obstruction.  Its witnesses, for every `j≥0` and `w>0`, are

```
A = 72*3^j*(64*w)-5,       B = 64*w+1,
T^6(A) = 216*3^j*(27*w)-5, T^6(B) = 27*w+1.
```

The target strictly increases, the auxiliary strictly decreases, both are
positive, and `A>B`.  The defined relation `rayEdge` records six **actual**
shortcut iterates, both affine branch identities (with target intercept
85), offset `-4` at both ends, and the inherited multiplier update `m'=3m`.
It is not an arbitrary relabeling of numerical endpoint pairs.
`ray_edge_exists` supplies every edge of the projected ray;
`no_uniform_ray_rank` excludes a rank into **any well-founded relation**
strictly decreasing on all these edges.  The CI consumer fixes these
definitions and public theorem types.

The stronger original-hard-family reachability and pre-descent bounds
above are a paper proof, supported by the exact finite CLI constructor;
they are **not** asserted as Lean theorems.  In particular the formal
local-edge result alone is not a theorem about every possible restriction
of the state graph to a chosen hard-family reachability predicate.
The paper lifting argument provides that connection for this particular
ray.  No single infinite positive orbit is inferred from finite lifts.

The installed CLI regression suite, root Lean build, and CI declaration
consumers pass.  The bounded formalization handoff is
[here](HANDOFF-2026-09-29-coefficient-ray.md).

## A projected three-cycle with an easy-lift limitation

Take `r=0` and the **generic negative control** `u=−5`.  Its exit
pair is `(A,B)=(36u−1,(9u+7)/2)=(−181,−19)`, with starting
`(m,d)=(8,−20)`.  The common shortcut map, extended to negative
integers by the same parity formulas, gives

```
A: -181,-271,-406,-203,-304,-152,-76,-38,-19,-28,-14,-7,-10,-5,-7,...
B: -19,-28,-14,-7,-10,-5,-7,-10,-5,-7,-10,-5,-7,-10,-5,...
```

At synchronized step 11 the pair is `(−7,−5)`.  Its next three
paired parity choices are `odd/odd`, `even/odd`, and `odd/even`.  The
corresponding projected states are exactly

| step | `(A,B)` | `(m,d)` |
|---:|---:|---:|
| 11 | `(−7,−5)` | `(8/9,−2/3)` |
| 12 | `(−10,−7)` | `(8/9,−17/9)` |
| 13 | `(−5,−10)` | `(8/27,−20/27)` |
| 14 | `(−7,−5)` | `(8/9,−2/3)` |

The values of `m` follow from the odd-step counts in the first eleven
steps (`4` for `A`, `6` for `B`), starting at `m=8`; each `d` follows
from `d=A+1−m(B−1)`.  The table also checks directly against the four
transition formulas.  This negative control is **not** an actual
hard-family parameter: `u=−5` would make `(2^3u−1)/9=−41/9`.

Nevertheless, every finite number of repetitions of this same
projected cycle is realized by a **positive actual hard-family** pair.
For exact `L=3`, the hard-family parameters satisfy `s≡7 (mod 8)`;
write `s=7+8t`.  Their positive odd quotient has the form

\[
u(t)={9q(s)+1\over8}=u_0+2Et,
\qquad E=12348281925\text{ odd}.
\]

For each `N`, choose arbitrarily large positive `t` with
`u(t)≡−5 (mod 2^N)`.  This is possible because `2E` generates
every odd residue modulo `2^N` from the odd base `u_0`.  The exit
values `A=36u−1`, `B=(9u+7)/2` then agree 2-adically with the
negative control to arbitrarily high precision.  Each shortcut step
loses at most one binary digit of precision, so a sufficiently large
`N` makes their first `h` **paired** parity choices agree for any
prescribed finite `h`.  The projected updates depend only on those
choices.  Thus the whole finite projected path, including as many
cycles as desired, occurs on positive hard-family parameters.

No single positive integer pair follows this infinite parity path.
From step 11 the target would have to repeat `odd, even, odd` forever.
On that branch `T^3(x)=(9x+7)/8`, and iteration gives
`T^{3j}(x)+7=(9/8)^j(x+7)`.  Integrality for every `j` forces
`8^j | (x+7)` for every `j`, hence `x=−7`, impossible for a
positive target.  The cycle is therefore a **spurious infinite path of
the projection**, despite arbitrarily long positive realizations.

This three-cycle separately rules out strict decrease on **every**
locally admitted single projected edge.  It has a crucial limitation:
the positive hard-family lifts of this `u=−5` control have already
descended below their original `n` by the time the projected cycle is
reached.  The pre-descent ray above is the relevant obstruction to a
rank intended only for hard states.  Neither result excludes a rank on
completed blocks that remembers the actual positive frontiers, the
parameter residue, or finite-prefix fuel.  They do not prove or
disprove convergence of any positive hard-family orbit.

The persistent discovery instrument is `experiments/repair_family.py`:
`q1-offset-trace r u --steps N` tracks the inherited primitive state,
and `q1-offset-ray K` constructs an actual hard-family parameter with
`K` six-step ray blocks.  `./experiments/repair_family.py test` runs
the subprocess regression suite, including the hand-derived local
anchor `(4603,65) → (5827,28)` and the congruence-defined hard lifts.
The constructor checks original target and auxiliary prefixes as well
as the aligned exit suffix, so an early target descent cannot silently
turn a proposed hard example into an easy control.
