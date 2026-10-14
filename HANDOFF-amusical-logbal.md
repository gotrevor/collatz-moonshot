# HANDOFF: amusical log balance

## 2026-10-13: objective complete — all three ratified targets proved

`CollatzMoonshot/AmusicalLogBalance.lean` is sorry-free.  The two remaining balance theorems
are closed with their ratified statements unchanged; the log-density implication was already
closed earlier in this treadmill.  The new finite-sum proof is isolated in
`CollatzMoonshot/AmusicalLogBalance/Estimates.lean`.

The decisive review finding was that the advertised logarithmic cutoff estimates are stronger
than the constants require.  For `N ≥ 9`, elementary interval-cardinality estimates suffice:

* exact even transport identifies the three-multiple weight with `2/3` of the even weight through
  cutoff `2 floor(N/3)`; its omitted even tail is at most `3/4`, hence contributes at most `1/2`;
* the odd branch is bijected to nonmultiples of three whose inverse is at most `N`; its pointwise
  reciprocal error telescopes to at most `2/3`, and the unmatched target tail is at most `2/3`;
* the two parity and divisibility partitions then give the even balance.  Combining it with the
  `1/2` even-to-three transport error gives the three-multiple balance;
* for `N < 9`, both statements follow from positivity, the relevant partition, and the explicit
  bound `sum_(n=1)^8 1/n < 3`.

All arguments are kernel proofs using `Finset.sum_bij`, finite sums, integer arithmetic, and real
inequalities.  No axiom, `native_decide`, heartbeat exception, or ratified-statement change was
introduced.  A diff against ratification commit `60e936c` confirms that `logWeight` and all three
theorem types are unchanged.

Verification run:

```text
lake build CollatzMoonshot.AmusicalLogBalance.Estimates
lake env lean CollatzMoonshot/AmusicalLogBalance.lean
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-logbal \
  --target CollatzMoonshot.AmusicalLogBalance
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-logbal \
  --target CollatzMoonshot.AmusicalLogBalance \
  --axioms CollatzMoonshot.Amusical.logWeight_even_balance
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-logbal \
  --target CollatzMoonshot.AmusicalLogBalance \
  --axioms CollatzMoonshot.Amusical.logWeight_three_balance
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-logbal \
  --target CollatzMoonshot.AmusicalLogBalance \
  --axioms CollatzMoonshot.Amusical.amusicalInfinitelyManyOrbits_of_logDensityZero
~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-logbal
git diff --check
```

The scoped and 8848-job full gates are FORMALIZE-tier green.  Each headline axiom ledger is
exactly `Classical.choice`, `Quot.sound`, and `propext`.

Current blocker: none.  The host predicate
`sorry-free:CollatzMoonshot/AmusicalLogBalance.lean` is met.

Next highest-value attack: none in this assignment.  No stretch objective was authorized; leave
the unrelated open amusical modules to their own treadmills.

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
