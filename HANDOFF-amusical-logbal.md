# HANDOFF: amusical log balance

## 2026-10-13: log-density implication closed

Closed `amusicalInfinitelyManyOrbits_of_logDensityZero` without changing its ratified statement.
The proof assumes finitely many nonnegative orbits, takes their finite set `T`, and uses convergence
to make every orbit's truncated log weight less than `log N / (|T| + 1)` at one common `N ≥ 2`.
Every integer in `[1,N]` belongs to its own orbit in `T`; summing the resulting pointwise cover
gives `harmonic N ≤ Σ O ∈ T, logWeight O N`.  The finite-limit bound makes the right side
strictly less than `log N`, contradicting `log N < log (N+1) ≤ harmonic N`.

Verification run:

```text
lake env lean CollatzMoonshot/AmusicalLogBalance.lean
```

This succeeds; its only warnings are the two remaining ratified `sorry`s.

Current blocker: the exact finite-sum transport estimates required by `logWeight_even_balance`
and `logWeight_three_balance` remain open.  There is no external blocker.

Next highest-value attack: formalize the exact even-to-multiple-of-three weighted bijection as a
helper in `CollatzMoonshot/AmusicalLogBalance/Transport.lean`.  Then prove a cutoff-tail lemma for
positive reciprocal sums.  These two ingredients directly feed both remaining statements; the
even balance additionally needs the two odd residue-class transports and their summable per-term
error.
