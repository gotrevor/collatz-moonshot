# HANDOFF: amusical log balance

## 2026-10-13: exact even-to-three transport proved

Added `CollatzMoonshot/AmusicalLogBalance/Transport.lean` and proved
`sum_multiples_three_transport`.  For every `U`-invariant set `S`, it gives the exact identity

```text
sum_{m in S, 3|m, 1<=m<=3 floor(N/2)} 1/m
  = (2/3) sum_{n in S, 2|n, 1<=n<=N} 1/n.
```

The proof is a kernel-checked `Finset.sum_bij` using `n = 2k -> U(n) = 3k`; surjectivity uses
the same formula backwards, invariance is applied in both directions, and all cutoff arithmetic
is discharged over integers.  No axiom, decision procedure, or statement change was introduced.

Verification run:

```text
lake env lean CollatzMoonshot/AmusicalLogBalance/Transport.lean
lake env lean CollatzMoonshot/AmusicalLogBalance.lean
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-logbal \
  --target CollatzMoonshot.AmusicalLogBalance
```

Current blocker: `logWeight_even_balance` still needs the odd-to-nonmultiple transport with its
summable per-term error and cutoff control.  `logWeight_three_balance` additionally needs only a
bounded reciprocal cutoff-tail lemma once even balance is available.  There is no external
blocker.

Next highest-value attack: add a generic lemma bounding reciprocal weight between cutoffs by the
unfiltered harmonic tail.  Use it to derive the `logWeight` form of the exact transport and close
`logWeight_three_balance` from `logWeight_even_balance`; then build the two odd residue transports.

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
