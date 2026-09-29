# Pairwise order transport: a sharp bound that does not exclude cycles

```sh
./experiments/pair_ordering.py test
./experiments/pair_ordering.py 00101
./experiments/pair_ordering.py 110
./experiments/pair_ordering.py 1110000 --multiplier 5
```

This tests the real-ordering part of the pairwise proposal after the [odd-prime denominator ledger](RESEARCH-2026-09-27-pair-denominators.md).  The repo's [Front B negative inventory](FRONT-B-ROUTES.md) already rules out treating rotation integrality or generic pair differences as an independent admission condition.  Here an exact order bound survives, but it holds for every primitive rational cycle and does not separate integer cycles.

## The mixed inversion graph

For an actual primitive `m`-cycle of the shortcut `3x+1` map, sort its distinct states.  The cycle step permutes that sorted list by one `m`-cycle.  On two even states the step scales their difference by `1/2`; on two odd states it scales it by `3/2`.  Both preserve order.  Thus every inversion of the permutation is a mixed odd/even pair.  For positive states its condition is exactly

```
o < e < 3o+1.                                           (1)
```

Let `I` count these pairs.  An `m`-cycle requires at least `m-1` adjacent transpositions, and the parity of any transposition factorization is `m-1` modulo 2.  Therefore

```
I >= m-1,                 I = m-1 (mod 2).              (2)
```

This is an exact consequence of *cycle closure and order*, without using rational or integer admission.  The lower bound is sharp: `10` gives `I=1`, the positive rational `11111000` gives `I=7` for `m=8`, and the positive **5x+1** integer control `1110000` gives `I=6` for `m=7` with condition `o<e<5o+1`.

Equality is false even for a positive primitive, fully closed **3x+1** rational cycle.  Word `00101` visits

```
(28,14,7,22,11)/23.
```

Its sorted states are `(7,11,14,22,28)/23`, and their actual images are `(22,28,7,11,14)/23`.  Both odd states reverse order with all three even states, so the mixed inversion graph is `K_(2,3)` and `I=6>m-1=4`.  This also saturates the obvious capacity `I<=|O||E|`.  The exact five-state cycle, denominator 23, positivity, distinctness, image list and six inversions are recorded as a finite `native_decide` certificate in `CollatzMoonshot/Obstructions/PairOrderingControl.lean`.  The general bound (2) remains a paper argument.

For negative states, condition (1) must be reversed where `3o+1<o`: the **negative 3x+1** cycle `110` has odd states `-5,-7` and even state `-10`; both pairs invert because `3o+1<-10<o`, giving `I=2=m-1`.  The CLI computes inversions from the signed gap product rather than applying the positive interval to negative states.

## What integer spacing adds

If all states are positive integers, the even integers strictly between an odd integer `o` and `3o+1` number exactly `o`.  Consequently

```
m-1 <= I <= sum_(o in O) o.                              (3)
```

For a generalized positive integer `qx+1` shortcut with odd `q>=3`, the upper bound is `((q-1)/2)*sum O`.  This is a genuine use of unit integer spacing, not just the rational closure equation.  It is weak for the cycle front: it gives equality for `1,2`, while any hypothetical nontrivial integer cycle already has large states.  The positive **5x+1** control has `I=6` and upper bound 258.  Equation (3) supplies no bound on the number of circuits or a contradiction with known cycle-size constraints.

The signed Vandermonde equation makes the algebraic limit of this branch explicit.  Let `C=binom(m,2)` and `k=|O|`.  Splitting the signed ratio `V(T(S))/V(S)` by parity yields

```
product_(e in E,o in O) (3o+1-e)/(o-e)
    = (-1)^(m-1) * 2^C / 3^binom(k,2).                 (4)
```

The right side is exactly the sign of the cycle permutation times the even-even and odd-odd slope factors.  Thus (4), its absolute-value version, and identities obtained by iterating the same transport are algebraic consequences of the individual edge equations and the fact that the states are permuted.  Real ordering supplies (2); integer spacing supplies (3).  All three hold automatically for the existing rational or generalized-map controls where applicable.  Repackaging (4) cannot add a second word-admission test.

**Verdict:** this bounded pass finds no cycle-excluding pairwise inequality.  Any further pairwise argument would need a new restriction on *joint* order, size and arithmetic of integer states that is not determined by the affine edge equations.  Neither the Vandermonde identity nor the inversion count provides it.  The pairwise branch should not remain an active proof lane on these observables alone.
