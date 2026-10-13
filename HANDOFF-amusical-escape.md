# Handoff: amusical escape (2026-10-13)

## Concrete advance

`evenFrequency_of_backwardNormal` is proved with its ratified statement unchanged.  The proof
partitions every coded-zero count by the finite fiber of `f`, applies `BackwardNormal` to each
exact block, and sums the resulting limits.  Balancedness and `w >= 1` reduce the limit
`3^(w-1) * (1/3)^w` to `1/3`.  An exact `Nat.count_add` identity then shifts the block stream by
`s`; the finite prefix vanishes after division by the sample length.

Thus `CollatzMoonshot/AmusicalEscape.lean` has two unresolved proofs rather than three.  The
entire Theorem N downstream chain and normality bridge are closed.  No `native_decide`, axiom,
heartbeat override, statement change, or long Lean line was introduced.  The pre-existing
untracked `CLAUDE.local.md` remains untouched.

## Exact verification

```text
lake env lean CollatzMoonshot/AmusicalEscape.lean
rg -n '.{101}' CollatzMoonshot/AmusicalEscape.lean
git diff --check
~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-escape \
  --target CollatzMoonshot.AmusicalEscape \
  --axioms CollatzMoonshot.Amusical.evenFrequency_of_backwardNormal
```

The direct elaboration succeeds with only the two remaining disclosed `sorry` warnings.  The
long-line scan and `git diff --check` have no findings.  The 8714-job real gate verdict is
`FORMALIZE-TIER GREEN`.  The new theorem's exact axiom ledger is
`[Classical.choice, Quot.sound, propext]`.

## Current blocker

Only `escape_forward` and `escape_backward` remain.  Both require a kernel-friendly analytic
iteration of the affine absolute-value branch bounds.  Nonperiodicity plus bijectivity first
makes the relevant orbit injective and hence eventually outside every bounded integer interval.
The remaining ledger must turn the per-step `+1` error into a uniformly small multiplicative
factor and contradict exponential decay forced by a persistent bit-average gap.

## Next highest-value attack

Attack `escape_forward`.  First prove reusable helpers for pairwise distinct iterates and eventual
escape from a finite integer interval.  Then choose a large integer threshold so
`1 + 1/(3X) <= 2^(delta/2)` and iterate `abs_amusical_le` over the late orbit, preferably after
taking logarithms to avoid rounding `logb 2 3 * k`.  Once this proof is stable, mirror the same
infrastructure for `escape_backward`, run the headline axiom audits, and call `box done` only when
the target file is sorry-free.
