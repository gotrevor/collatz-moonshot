# Borrowability requires overshoot already at 23

```sh
./experiments/borrowability_descent.py test
./experiments/borrowability_descent.py 23
./experiments/borrowability_descent.py scan 85 300
```

The restricted palette repairs the published 71 certificate, but that
finite result does not explain which odd 3-free labels it can borrow in
general.  A natural proposed induction is: to borrow a new label `u`, find a
quadratic exchange whose input labels `c,d` are both smaller than `u` and
whose output contains `u`.  This precise induction fails at `u=23`, the
first 3-free odd label outside the unit seeds and the label 13 supplied by
the essential cubic.  Since the unit seeds reach 83, this early failure
alone does not rule out strong induction with all labels through 83 as
its finite base.

Write `r_v=2v/(3v+1)`.  If `r_23 r_b=r_c r_d` with positive odd `c,d<23`,
cross-multiplication gives

```
D(c,d) b = 70 c d,
D(c,d) = 23(3(c+d)+1)-3cd.
```

There are eleven positive odd labels below 23, hence 66 unordered choices
of `c,d`.  Positivity is immediate from
`D=23(3c+1)+3d(23-c)>0`.  For every pair, `D(c,d)` does **not** divide `70cd`.
This excludes every positive integer companion `b`, with no bound on its
height.  A near miss is `(c,d)=(13,17)`, which forces `b=119/11`.  The
independent direct-formula CLI and the repository's complete quadratic
neighbor routine agree.  The latter has 31 nontrivial interactions with
`r_23`; none has both opposite labels below 23.

Among 3-free quadratic interactions, the smallest possible maximum of the
opposite pair is 49, attained by

```
{23,245} <-> {37,49}.
```

Thus a first introduction of `r_23` through a quadratic rule must already
have access to a label at least 49 on its input side.  This is a precise
overshoot requirement for **that step**, not an obstruction to borrowing 23:
the saved closure introduces it via `{35,65}<->{23,1625}`, starting from
borrowable 35 and 65.  The unit palette has large seed labels, so it can
cross the height barrier.

The same exact criterion fails **above** that finite base.  For `u=85`,
`3u+1=256`, so an odd companion `b` requires `D_85(c,d)` to have exactly
eight factors of 2.  Among 3-free odd `c≤d<85`, only these pairs pass that
necessary test:

| `c,d` | `D_85(c,d)/256` | `cd mod (D/256)` |
|---|---:|---:|
| 5, 53 | 55 | 45 |
| 37, 53 | 67 | 18 |
| 53, 53 | 73 | 35 |

None yields integral `b`, so 85 has no two-smaller-input quadratic
introduction using 3-free labels.  Its failure remains true even if
3-divisible input labels are allowed.  The restricted 3-free scan of 85
through 299 finds 60 failures among 72 candidate labels.  It is a bounded
test of this one-step descent only; for example 95 succeeds via
`{19,29}<->{13,95}`.  It says nothing by itself about nonmonotone
borrowability or a different parametric induction.

[BorrowabilityHeight23.lean](CollatzMoonshot/Obstructions/BorrowabilityHeight23.lean) now proves the cross-multiplied quadratic identity impossible for every natural companion b.  Its finite divisibility check and exact Nat-subtraction identity feed the unbounded theorem `no_quadratic_cross_identity_23`.  The external Python CLI suite exercises the 23 obstruction, the hand-computed 119/11 near miss, a positive control, and the exact 85 table.  Three tests pass.  The 85 obstruction remains a Python certificate and paper argument.

The surviving general question is whether the unit seeds plus quadratic
rules and the essential cubic can supply *every* 3-free odd label through a
nonmonotone closure.  This note neither proves that nor identifies a global
invariant excluding one.
