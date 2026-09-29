# Bounded Lean task: exact cubic carry prefixes

Work only in `CollatzMoonshot/Obstructions/CubicCarry.lean`, starting from the staged skeleton.  It imports the current `SignedFlow` and `CubicPeel` modules.  Preserve the definition of `neighbor` and all five frozen theorem statements.  They describe arithmetic identities and one convergence transfer; none asserts convergence of `cubicN` or a decreasing repair rank.

The affine data from `CubicPeel` give the following six iterates of `cubicN s` for every natural `s`:

| `j` | `tstep^[j] (cubicN s)` |
|---:|---:|
| 0 | `25542881863 + 39026668800*s` |
| 1 | `38314322795 + 58540003200*s` |
| 2 | `57471484193 + 87810004800*s` |
| 3 | `86207226290 + 131715007200*s` |
| 4 | `43103613145 + 65857503600*s` |
| 5 | `64655419718 + 98786255400*s` |
| 6 | `32327709859 + 49393127700*s` |

All progression slopes before each parity check are even, so the parity is the parity of the displayed constant: odd, odd, odd, even, odd, even.  Separately, `cubicQ1 s = 1795983881 + 2744062650*s` is odd; prove that parity locally because the existing `cubicQ1_odd` is private to `CubicPeel`.  Then

```
tstep (cubicQ1 s) = 2693975822 + 4116093975*s;
neighbor s = 86207226304 + 131715007200*s.
```

Derive the neighbor affine coefficients by `omega` from `two_tstep_odd`.  The orbit table proves the first, second and fourth targets by elementary arithmetic.  In particular the third iterate is even and differs from `neighbor` by 14; after two neighbor halvings the fifth actual iterate differs by `16*tstep(cubicQ1 s)-10`.

For unboundedness, choose `s=B`.  The gap is `16*tstep(cubicQ1 B)-10`, whose positive affine slope dominates `B`; `omega` suffices after rewriting the finite iterate identities.  Do not infer a dynamical separation beyond the displayed finite prefixes.

For convergence transfer, prove `tstep (2*u)=u` for natural `u`; five applications give `tstep^[5] (neighbor s)=tstep(cubicQ1 s)`.  Apply `SignedFlow.reachesOne_step_iff` to the assumed convergence of `cubicQ1 s`, then propagate backward across five steps.  A small general helper `reachesOne_of_iterate` is fine.  The target is deliberately only the neighbor, not `cubicN`.

Acceptance: all five frozen theorems compile without `sorry` or additional axioms.  This is a one-lap arithmetic target; if a proof needs helper parity facts or iterate-rewrite facts, add them locally but do not expand the theorem scope.  Parent runs the normal build and audit.


Operator scope: Opus/low, at most two laps, no Aristotle.  Dependencies are warm and the shared store was checked this session.  Own only CubicCarry.lean and HANDOFF-2026-09-29-cubic-carry.md.  Preserve the neighbor definition and all five theorem statements exactly.  Parent owns all other source and documentation.  Do not change SignedFlow or CubicPeel.  Build the module and root, commit green, then call box done --green immediately.  No successor work or extra research targets.
