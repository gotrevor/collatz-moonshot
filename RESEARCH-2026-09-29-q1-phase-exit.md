# Variable-depth repair: accumulated contraction and the re-entry problem

> **Re-entry follow-through:** [Full run and reset accounting](RESEARCH-2026-09-29-q1-run-macro.md) shows both growing and descending subfamilies.  The actual exit obstruction, one-halving expansion, and equivalence of normalized-weight decrease to size decrease are now formalized.  No reusable inherited-offset reset was found.

## Decision

Continue with one bounded mechanism test: find a closed family of full affine
frontier states and a decreasing **completed-block** rank.  The failed rank at
an individual exit does not justify abandoning this test.  Neither does the
bounded-splicing obstruction supply evidence that the adaptive construction
works.  No new Lean campaign is warranted until there is a surviving transition
to formalize, or a precise negative theorem worth preserving.

The pairwise-cycle branch still lacks a cycle-excluding arithmetic inequality;
the anchored-operator branch still lacks an independent estimate rather than
an orbit-height reformulation.  Neither currently offers a more concrete next
mechanism than the exit map below.  These remain separate research gaps.

## Exact complete-block calculation (paper, not yet Lean)

Use the actual shortcut map `T`, and write `9q+1=2^L u`, with `u` positive odd
and `L≥2`.  The aligned frontiers are

```
A0 = T^6(n) = 2^(L+1)*u - 1
B0 = T^2(q) = 1 + 2^(L-2)*u.
```

These formulas also define generic positive integer pairs without requiring
that `(2^L u-1)/9` be an integer or belong to our hard family.  Generic controls
must not be presented as actual hard-family parameters.

There are `r=floor((L-2)/2)` regular two-step rounds.  At their end,
`A+1=M(B-1)`, with `M=8*3^r`.  Each regular round multiplies
`R(A,B)=(A+1)(B-1)^3` by `243/256`.

For odd `L=2r+3`, put `v=3^r u`.  Just before the exit block,

```
A+1 = 16*3^r*v,    B = 1+2v.
```

Both frontiers take two odd steps at exit, giving

```
Af+1 = 36*3^r*v,    Bf = (9v+7)/2.
```

Consequently the ratio over the **whole phase plus exit** is

```
R(Af,Bf)/R(A0,B0)
  = (243/256)^r * (9/4) * ((9v+5)/(4v))^3.
```

The exit factor is large but bounded independently of `r` and `u`; the phase
factor tends to zero.  More precisely, the full ratio is greater than one for
`r≤62`, and less than one for `r≥63`, uniformly in positive odd `u`.  Both
factors decrease in `r`, and the second decreases in `u`.  The boundary is
settled by the exact rational comparisons

```
(243/256)^62 * (6561/256) > 1
(243/256)^63 * (9/4) * ((9*3^63+5)/(4*3^63))^3 < 1.
```

Thus odd phases with `L≥129` pay for their exits.
This is a uniform statement in positive odd `u`, not a numerical trend over
selected starts.  The earlier exit counterexample rules out per-block
monotonicity for the smaller blocks; it does not rule out amortization over
these longer blocks.

For even `L`, the previous note proves that the two-step exit contracts on the
actual hard family, so adding the preceding regular rounds also contracts.

## Why this still is not an induction

At the odd exit the retained affine equation is

```
2*(Af+1) = M*(2*Bf-7).
```

It is no longer `Af+1=M*(Bf-1)`.  Restarting the old phase rule silently would
drop an additive offset.  There is a stronger immediate nonclosure statement:
since `Bf≥8`,

```
M/3 < (Af+1)/(Bf-1) = M*(Bf-7/2)/(Bf-1) < M.
```

No canonical multiplier `8*3^j` lies strictly between `M/3` and `M`.  Thus
even choosing a new canonical exponent cannot directly restart the same rule
at this endpoint.  Further actual steps or a larger state class remain possible.

The auxiliary may also reach 1 with the target still
above 1: the generic actual pair `(31,5)` goes through `(71,4)` to `(161,1)`.
Its polynomial weight is then zero, so this weight alone does not encode the
required terminal condition.

The next target must therefore handle **re-entry**, not merely absorb one exit
cost.  A useful state contains both actual frontiers and the complete affine
relation, including its offset.  A successful rule must:

1. Take a finite, parameter-dependent number of actual steps or supply an exact
   signed boundary to an induction-known convergent vertex.
2. Return to a specified state class on which another rule is available.
3. Decrease a well-founded rank of that full state over the completed block.
4. Have a terminal condition that establishes the target connection, including
   the case in which the auxiliary reaches 1 first.

Closure and decrease must be proved on the states actually generated.  A new
name for the paired Collatz orbit, or a decreasing rank conditional on eventual
meeting, does not meet this target.

## What large precision does not buy

Write `E=12348281925`, so `(9q(s)+1)/2=8081927465+E*s`.
For any fixed exact odd valuation `L=2r+3`, the admissible parameters form one
progression `s=s0+2^L*t`.  Their odd quotients have the form
`u=u0+2E*t`.  Thus

```
Bf = Bf0 + 9*3^r*E*t.
```

This slope is odd.  The exit auxiliary realizes every residue modulo every
power of two, hence every finite shortcut parity prefix.  Increasing `L` does
not force a favorable finite parity suffix after exit.  The target and
auxiliary remain arithmetically coupled, so this observation does not exclude
a rule using their full joint state.  It does exclude treating large initial
precision as automatic control of the auxiliary's next phase.

## Provenance

The all-depth separation and the sparse 18-step descent are already proved in
[Q1Coalescence.lean](CollatzMoonshot/Obstructions/Q1Coalescence.lean).
The complete-block calculation and re-entry analysis in this note are paper
results.  The general supply result remains
[Applegate–Lagarias](https://arxiv.org/abs/math/0411140); more multiplicative
supply by itself does not supply the missing orbit connection.

## Persistent diagnostic

`experiments/repair_family.py q1-phase-exit L u` computes the exact initial,
pre-exit and post-exit frontiers, cross-checks them against actual shortcut
iteration, and reports rational weight ratios, the odd-exit affine identity,
canonical re-entry, and whether the inputs belong to the hard `q1` family.
It does not search for convergence.  Its external CLI tests retain the
hand-computed pairs `(63,9) → (143,7) → (323,17)` and
`(31,5) → (71,4) → (161,1)`, an actual hard-family anchor at `s=3`, and the
exact rational inequalities at the 62/63-round boundary.
