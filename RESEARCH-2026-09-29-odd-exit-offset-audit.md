# Odd-exit affine offset: exact update and short re-entry obstruction

This audits the paper odd-exit state of `RESEARCH-2026-09-29-q1-phase-exit.md`.  It does not assume that either unknown target frontier converges.  A real completed-block rank remains open.

Put `x=3^(r+2)u`, where `r≥0` and `u` is positive odd.  The odd-exit frontiers are

```
A = 4*3^r*x−1,       B=(x+7)/2,       x≥9 and x is odd.
```

Write `X=A+1`, `Y=B−1`, and `M=8*3^r`.  Their exact relation is

```
X=M*Y−(5/2)M.                                       (1)
```

The additive offset is an integer (`(5/2)M=20*3^r`) and cannot be discarded.  For an arbitrary actual pair satisfying `X=mY+d`, each shortcut step updates the full affine data as follows.  Use `p_A=3,e_A=0` for odd `A` and `p_A=1,e_A=1` for even `A`; use `p_B=3,e_B=2` for odd `B` and `p_B=1,e_B=−1` for even `B`.  Then

```
X'=(p_A X+e_A)/2,       Y'=(p_B Y+e_B)/2,
m'=(p_A/p_B)*m,
d'=(p_A*d+e_A−m'*e_B)/2.                           (2)
```

This is an exact rational-affine state transition with parity supplied by the actual vertices.  It is bookkeeping, not a decrease theorem.  On an infinite fixed-parity affine subprogression, after `i` steps from `A` and `j` from `B`, the slope ratio is `M*3^(a−b)*2^(j−i)`, where `a,b` are the odd-step counts.  To equal a canonical multiplier `8*3^J`, unique factorization forces `i=j` and `J=r+a−b`.  This excludes an **unequal-time fixed-word affine reset** to the old canonical class on any infinite subprogression.  A single isolated parameter can still satisfy an accidental numerical equality; the slope claim is not a pointwise exclusion.

## Pointwise failure of the first two synchronous resets

The first two `A` steps are always odd, giving `A₂+1=9*3^r*x`.  The auxiliary's first two steps split into all four odd residue classes of `x` modulo eight:

| `x mod 8` | `B₁` | `B₂−1` | slope-matched canonical `8*3^J` | actual ratio interval |
|---:|---|---|---|---|
| 1 | `(x+7)/4` | `(x−1)/8` | `J=r+2` | `8*3^(r+2) < (A₂+1)/(B₂−1) < 8*3^(r+3)` |
| 5 | `(x+7)/4` | `(3*x+17)/8` | `J=r+1` | `8*3^r < (A₂+1)/(B₂−1) < 8*3^(r+1)` |
| 3 | `(3*x+23)/4` | `(3*x+15)/8` | `J=r+1` | `8*3^r < (A₂+1)/(B₂−1) < 8*3^(r+1)` |
| 7 | `(3*x+23)/4` | `(9*x+65)/8` | `J=r` | `8*3^(r−1) < (A₂+1)/(B₂−1) < 8*3^r` for `r≥1`; for `r=0`, the ratio lies in `(0,8)` |

All intervals are strict.  For example, in the last branch the ratio is `8*3^r · 9x/(9x+65)`; `x≥63` there, so its fractional factor lies strictly between `1/3` and `1`.  The other branches give `x/(x−1)∈(1,3)` or `3x/(3x+c)∈(1/3,1)`.  Hence **no positive odd-exit state has canonical re-entry after two synchronized steps**, even if the exponent is chosen separately in each residue branch.  After one synchronized step the same conclusion holds: for `x≡1 (mod 4)` the ratio is `8*3^(r+1)·x/(x+3)`, strictly between neighboring canonical values; for `x≡3 (mod 4)` it is `8*3^r·3x/(3x+19)`, likewise between neighbors (or below `8` when `r=0`).  The original exit itself was already excluded in the repository note.

This is a four-branch obstruction for the hard family, not just a generic pair calculation.  At fixed exact odd valuation `L=2r+3`, the admissible hard parameters have `u=u₀+2E t` with `E=12348281925` odd.  As `t` varies modulo four, `u` runs through all odd residues modulo eight; multiplication by `3^(r+2)` permutes them.  Thus no state containing only `(m,d)` from (1) can prescribe a unique next branch.  It must retain at least parity/carry data or allow all four successors.  The two-step result does not exclude later or asynchronous re-entry, a different canonical family, or a signed-boundary repair.

## What auxiliary shrinkage pays for

Across an odd phase plus exit, `A_f+1` grows by the exact factor `(9/4)^(r+1)` relative to `A₀+1`.  The proved contraction of `(A+1)(B−1)^3` for `r≥63` is therefore entirely paid for by the auxiliary factor shrinking.  This is a legitimate amortized scalar inequality, but it does not itself move the target frontier into the known convergent basin.

There is an exact calibration at any **fresh normalized reset**.  Put `d=(9q+1)/4`.  The normalized pair is `(8d−1,d+1)`, with old weight `8d⁴=(9q+1)^4/32` and terminal-faithful weight `8d(d+1)³`.  Both are strictly increasing in positive `d`, hence in `q` (and in the corresponding hard `n`, since `128q=9n+1`).  A completed block returning to this same normalized family decreases either weight only if its *new* auxiliary parameter `q'` is genuinely smaller than `q`.  The reduction in the current `B` during a phase is not transferable credit for a fresh reset by itself.  This calibrates a restricted rank architecture; it does not rule out a different state class or a boundary-changing repair.

The terminal issue occurs on a genuine odd-exit pair in the generic state class: `r=0,u=1` gives `(A,B)=(35,8)`.  After three actual steps it becomes `(40,1)`: `35→53→80→40`, while `8→4→2→1`.  The old weight is then zero despite `A=40`; the terminal-faithful variant `(A+1)B^3` has dropped from `36·8³=18432` to `41`, still with no target connection.  This pair is **not** an admissible hard-family parameter because `(2³u−1)/9=7/9` is not integral.  It is a control for any rank claimed on the larger generic affine-offset state class, not evidence about a particular hard start.

There is a smaller alternate induction-known label at the exit:

```
C=3^r*u=(2B−7)/9,    B=(9C+7)/2,
A+1=4*3^(r+2)*C.                                    (3)
```

Whenever the original hard `n` is integral, `n=(1024·4^r u−137)/81`, and `0<C<n<A`.  The inequality follows by comparing the displayed positive coefficients.  Thus strong induction knows that `C` converges, but (3) gives no actual-edge path or signed boundary from `A` to `C`.  For `r≥1`, `3|C`, so the unrestricted 3-free unit-supply theorem cannot be invoked to borrow `C` as a value-one factor.  As a path endpoint it remains available under induction.  A reset through `C` would need a new transition theorem for the affine target `4*3^(r+2)C−1`, not just the scalar equality (3).

A further fixed-depth extension alone does not qualify as a new mechanism.  The next accepted target is a rule for an explicitly closed inherited-offset state class, or a directed connection to a smaller induction-known vertex.  It must retain the affine offset, establish its parity conditions and exact edge boundary, and account for auxiliary reset and the terminal case `B=1`.  No such rule was found in this audit.  The pointwise one- and two-step obstructions in this note remain paper results.
