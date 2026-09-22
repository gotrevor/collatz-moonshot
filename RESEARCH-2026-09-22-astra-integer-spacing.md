# Independent audit: integer spacing and the information lost by sorting

Prepared by Astra/Codex against collatz-moonshot commit `bce759a`.
File ownership was agreed with Fable in mailbox messages `20260922T180035Z-fable-4da80de9-9387-4a2e-bbbc-f9d7b9118dc9.md` and `20260922T190207Z-fable-efde3b7e-6829-4a02-ae40-95de54ab0e47.md`.
Fable independently re-derived the base obstruction and its full-numerator strengthening in those messages.  The mixed-prefix extension below was sent separately for review.
No helper, proof lap, or implementation change is authorized by this note.

## Result

The linear run lower bound does not imply StoppingCorrect.  I found no missing cycle-exclusion mechanism in the reviewed repo material.

I independently tried a positive-integer constraint that the minimum-only estimates discard: distinct odd orbit values have spacing at least two.  It gives a valid product bound, proved below.  But an explicit unbounded family of first-crossing words, all with odd runs of length at most two, passes both this bound and the exact real inequality `D*n <= N` at integer candidate starts `n = 8*K+1`.  The full bound retains the exact numerator and the nonnegative rational overshoot; it still does not impose an integer overshoot.  Full admission is missing.  This disproves sufficiency of the stated relaxation, not of all arguments involving spacing, magnitude, or carries.

The family below is used as an adversary, not as a revival of the retired Christoffel-word residue-signature approach.

## 1. Logical audit

Let `S(n,m)` mean `n >= 2`, `At n m`, and `T^m(n) >= n`.  Put `K = ones`, `r = oddRunCount`, `D = 2^m - 3^K > 0`, `N = numer`, and `u = 2^m/3^K`.

For fixed positive epsilon:

* `N_epsilon`: every survivor has `r >= epsilon*K`.
* `C_epsilon`: no survivor has `r >= epsilon*K`.
* `StoppingCorrect <=> N_epsilon and C_epsilon`.

This is a split of the survivor population, not a reduction of the many-run half.  A survivor with many runs is a counterexample to C_epsilon, not a witness satisfying C_epsilon.

The actual frontier implications remain distinct:

* `StoppingCorrect -> NoNontrivialCycle`, already proved in `FirstCrossingCycles.lean`.  A positive cycle has a subcritical full period, so its minimum has a first crossing by that period.  It cannot descend below itself.
* `StoppingCorrect and CrossingExists -> Conjecture`, already proved in `FirstCrossing.lean` by descent/strong induction.
* CrossingExists by itself allows positive cycles: every positive periodic orbit crosses eventually.  It supplies a coefficient crossing, not the required descent there.
* A never-crossing positive orbit is unbounded: if bounded, deterministic iteration on a finite set becomes periodic, and the positive cycle's subcritical multiplier eventually overwhelms the fixed initial prefix.
* Conversely, a divergent orbit could have finite coefficient crossings that fail to descend.  Excluding never-crossing orbits does not by itself exclude that possibility.
* A finite first-crossing failure need not be a Collatz counterexample: it may descend and reach 1 later.  Do not identify StoppingCorrect with Conjecture.

C_epsilon excludes the cycles whose minimum's first-crossing prefix has at least epsilon*K runs.  The number of circuits in the full cycle is at least that prefix run count, but the converse inclusion does not follow.  The existing fixed-circuit pincer does not provide a uniform exclusion of this subclass.

## 2. The candidate: spacing of actual distinct odd values

Assume S(n,m), and additionally that the states before the crossing are pairwise distinct.  Let `x_0,...,x_(K-1)` be their odd values, in time order.

The start must be odd: an even start crosses and descends at step one.  Every proper prefix is coefficient-supercritical, and its additive numerator is nonnegative, so every pre-crossing state is at least n.  Since the odd values are distinct positive odd integers, their increasing rearrangement satisfies

    x_(i) >= n + 2*i,  0 <= i < K.

The exact multiplicative identity along the actual trajectory is

    T^m(n)/n = (3^K/2^m) * product_i (1 + 1/(3*x_i)).

For a survivor, writing E = T^m(n)-n, this gives

    u*(1 + E/n)
      = product_i (1 + 1/(3*x_i))
      <= P_K(n) := product_(i=0..K-1) (1 + 1/(3*(n+2*i))).       (SP)

In particular, `u <= P_K(n)` is necessary.

This consumes actual integer admission: parity, positivity, and distinctness of the realized states imply spacing two.  Mere rational positivity supplies none of that spacing.  It is stronger than replacing each x_i by n separately.

### Exactly what this keeps and discards

The minimum-only bound forgets that K distinct odd values cannot all sit at n.  Sorting retains that occupancy restriction and all reciprocal ranks.

But sorting discards which value occurs at each time.  The affine relations between successive states, the specified word, and the starting residue are no longer enforced.  Formula (SP) is a consequence of full admission, not a substitute for it.  The obstruction in section 3 quantifies that loss even when the exact numerator is retained through the rational quantity `E=(N-D*n)/2^m`.  Then its left side is exactly `1+N/(3^K*n)`, not merely u.

The first-crossing condition does not itself guarantee distinctness.  A repeated state inside the prefix gives a positive cycle, and the orbit-below-a-cycle control exhibits exactly this branch.  Thus any attempted universal use must handle repeats separately.  Under NoNontrivialCycle, no repeat can occur in such a prefix: its states are at least n >= 2, and reaching the trivial cycle before crossing would force a subsequent proper-prefix value 1, or a descending endpoint, contradicting the survivor conditions.

For a minimum of a simple positive cycle, the first crossing lies within one least period, so its pre-crossing states are distinct.  The candidate does apply to that cycle-minimum case; it simply does not yield a contradiction.

## 3. An all-length obstruction to the proposed relaxation

For each integer i >= 0 define p_i by

    2^(p_i) <= 3^i < 2^(p_i+1).

Given K >= 2, let `m = p_K+1` and put odd letters at exactly the positions

    p_0, p_1, ..., p_(K-1)

in a word v_K of length m.  Positions start at zero.

### The word is first-crossing and has many short runs

The positions strictly increase.  Between positions p_(i-1)+1 and p_i the word has i odd letters, and every such proper prefix of length j satisfies `2^j <= 2^(p_i) <= 3^i`.  After the last odd letter the same argument uses p_K.  At m, `3^K < 2^m`.  Thus v_K is a first-crossing word.

Since 2 < 3 < 4, each difference p_(i+1)-p_i is 1 or 2.  Moreover 3^2 > 2^3 implies p_(i+2)-p_i >= 3, so two consecutive differences cannot both be 1.  Consequently every odd run has length at most two, and

    r >= K/2.

The internal even runs have length one and the terminal even run has length one or two.  More precisely, `r = p_(K-1)-K+2`, hence `r/K -> log_2(3)-1`.

### Its exact numerator leaves a linear-size integer start available

The numerator formula gives

    N/3^K = sum_(i=0..K-1) 2^(p_i)/3^(i+1).

Every summand lies in `(1/6, 1/3]`, so

    K/6 < N/3^K <= K/3.                                      (NUM)

A stronger upper bound comes from pairing adjacent terms.  Write `a_i=2^(p_i)/3^i`.  If the next position gap is one, `a_(i+1)=2*a_i/3`, and `a_i+a_(i+1)<=5/3`.  If the gap is two, `a_(i+1)=4*a_i/3<=1`, hence `a_i<=3/4` and their sum is at most 7/4.  After dividing by three, each adjacent pair of numerator summands is at most 7/12.  An unpaired last summand is at most 1/3.  Thus, for both parities of K,

    S := N/3^K <= (7*K+1)/24.                               (PAIR)

There are arbitrarily large K with `1 < u = 2^(p_K+1)/3^K <= 101/100`.  This follows directly from the repo's proved `two_pow_approx_three_pow_from_above`: take its approximation parameter at least 100 and its exponent lower bound arbitrarily large.  A ratio at most 101/100 forces the supplied power of two to be the first one above 3^K, so its exponent is p_K+1.  No randomness or normality assumption is involved.

For each such K, let `n=8*K+1`, a positive odd integer.  Then (NUM) gives

    D*n/3^K = (u-1)*n <= (8*K+1)/100 < K/6 < S.

The strict middle inequality holds for every K >= 1.  Thus `D*n<N`, and the exact rational `E=(N-D*n)/2^m` is positive.

The FULL spacing inequality also passes.  The reciprocal-sum bound (Cauchy, or harmonic mean at most arithmetic mean) gives

    P_K(n) >= 1 + (1/3)*sum_i 1/(n+2*i)
           >= 1 + K/(3*(n+K-1)).

For K>=2 and n>=7*K+1,

    (7*K+1)/(24*n) <= K/(3*(n+K-1)),

because after clearing denominators this is precisely `(K-1)*n >= (K-1)*(7*K+1)`.  Our n=8*K+1 satisfies it.  Combining with (PAIR),

    u*(1+E/n) = 1+S/n
              <= 1+(7*K+1)/(24*n)
              <= 1+K/(3*(n+K-1))
              <= P_K(n).

Therefore this unbounded family passes simultaneously:

* exact first-crossing ballot structure;
* a linear run lower bound, with all odd runs at most two;
* the exact word numerator and the inequality D*n < N;
* positive odd integer n, arbitrarily large;
* the FULL necessary distinct-integer-spacing inequality (SP), retaining the exact numerator through a nonnegative rational E.

**Not asserted:** these n realize v_K; their overshoots are integers; every member fails admission; or any member is a genuine survivor.  The missing statement is exactly the full congruence/temporal realization.  This is an obstruction to the specified scalar relaxation, not a counterexample to Collatz or a theorem against stronger order-sensitive packing arguments.

### Hand anchor, without a search

K = 5 gives positions `(0,1,3,4,6)`, word `11011010`, m = 8, r = 3:

    N = 81 + 54 + 72 + 48 + 64 = 319,
    D = 256 - 243 = 13,
    n = 21,
    D*n = 273 < 319,
    E = (319-273)/256 = 23/128,
    u*(1+E/n) = 1+319/5103 < 16/15 <= P_5(21).

The last bound is by the reciprocal-sum inequality on `21,23,25,27,29`, whose average is 25: `P_5(21)>=1+5/(3*25)=16/15`.  The strict comparison is `15*319=4785<5103`.  This small anchor need not satisfy the conservative sufficient parameter choice n=8*K+1 used for the unbounded family.

But the full realizing residue is 123 modulo 256: `243*123+319 = 256*118`.  The actual trajectory is

    123,185,278,139,209,314,157,236,118.

Thus its least positive realizing start is already above `N/D = 319/13`, and it descends.  The false candidate n = 21 does not realize the word; its overshoot 23/128 is not integral.

An earlier mailbox sketch used n=5 and only `u<=P_K(n)`.  That example fails the stronger exact-numerator version of (SP), so it is superseded by n=21 and the full-bound argument above.  This correction matters: dropping the overshoot would discard available information before evaluating the candidate.

## 4. Recorded controls

| Control | What the argument actually says |
|---|---|
| Short-run rational family, and P6-passing family | Rational vertices have no integer spacing-two guarantee.  A fixed-prefix test cannot confer it.  These families are not excluded by applying an integer-only lemma to their rational vertices.  Their known admission obstructions stay separate. |
| 2305/2313 prefix-remainder pair | The shared 46-step segments are not first crossings: both starts cross at step 2, reaching 1729 and 1735 respectively.  The 46-step segments dip to 103, so their values cannot be bounded below by the original start.  The proof does not discard their prefix remainders or claim their shared trunk decides admission. |
| Ballot coalescence counterexamples | Distinctness here concerns states of one trajectory.  It asserts no injectivity between different starts, words, or numerators.  Coalescence between the recorded distinct starts is allowed. |
| Mersenne q=12, next-run=6 | No lower bound on the odd cofactor beyond positivity, and no claim that adjacent long runs force extra magnitude, is used.  The example remains allowed. |
| Powers and repetitions | A whole first-crossing word cannot be a proper power.  Internal repeats of states can still occur; they are a separate cycle branch, not a hypothesis silently erased. |
| Proportional run scaling | Section 3 is an unbounded, explicitly proved obstruction with r >= K/2.  It is not a finite scan extrapolation. |
| Trivial positive cycle | At n=1, K=1, m=2, u=4/3 and P_1(1)=4/3.  Equality is allowed; the CST domain excludes n=1. |
| 5n+1 cycle at 13 | Its first-crossing word is 1110000 and its odd values are 13,33,83.  The exact product is `(66/65)*(166/165)*(416/415) = 128/125`.  The spacing upper bound substitutes 13,15,17 and is larger.  The cycle passes, as a sound inequality must. |
| 5n+1 start 5 | Its long first-crossing prefix repeats cycle states; it does not satisfy distinctness.  It cannot be discarded by calling its primitive word a nonrepeating orbit. |
| Negative cycles; 3n-1 | The positive-floor/positive-factor comparison cannot be extended to negative states.  For positive 3n-1 trajectories, the product factors are `1-1/(3*x_i)`, so any finite coefficient crossing descends.  That does not give CrossingExists: 5,7,10 is the recorded never-crossing cycle. |

## 5. Scope corrections to Fable's negative conclusions

The single-congruence lemma is correct: `D*n+2^m*E=N` with integer n,E and n>=2 supplies full admission.  But equivalence to one congruence does not prove that no useful estimate can be derived by considering its solutions in multiple coordinates.  Counting equations is not a bound on the strength of consequences.  The spacing attempt fails for the explicit reason in section 3, not because a second congruence was unavailable.

The 5n+1 control shows that a universal survivor-exclusion argument cannot use hypotheses all satisfied by those survivors.  It does not prove the only possible distinguishing inputs are ballot entropy and a verified range.  Coefficient-specific arithmetic remains logically available, though no new useful estimate is supplied here.

Likewise, square-root error describes a barrier for the particular discrepancy/large-sieve estimates considered.  It is not a universal lower-bound theorem on every counting method.  A proof of emptiness needs an upper bound on the nonnegative integer count strictly below one, which may be a one-sided structural bound rather than an equidistribution estimate.

Finally, for a fixed map and fixed seed, the orbit-below-a-cycle construction has a determined first-crossing lap count.  The 5n+1 seed 5 gives 39 laps, not an unbounded family of first crossings obtained merely by letting the number of laps vary.  Such varying prefixes are valid trajectories, but only one is its first crossing.  An unbounded family requires varying the cycle or seed and checking the rotation/crossing hypotheses anew.

## 6. Fable's proposed repair: exact prefix plus unordered tail spacing

Fable asked whether keeping the first j letters' exact realizing residue and then applying spacing to the rest repairs the candidate.  The answer below is negative for a specified relaxation and window scale.  It is not a claim about every mixed argument, and it does not reopen a fixed-prefix proof campaign.

Let j=j(K)>=1 satisfy

    2^j * j^2 = o(K).

For example, `j=floor((log_2 K)/2)` works.  Use the same first-crossing words v_K and arbitrarily large K with `1<u<=101/100`.

### The prefix is genuinely realized by distinct positive integers

Choose n in the interval `[10K,12K]`, in the exact realizing residue class modulo 2^j of the first j letters of v_K.  This class is odd.  There are `2K/2^j+O(1)` choices.

For the prescribed prefix, each time-t state is an affine function of n with slope `3^(K_t)/2^t`.  Slopes at different times are unequal: equality would require a nontrivial equality of powers of two and three.  Thus any pair of times among `0,...,j` can have equal states at at most one value of n.  Excluding those at most `j(j+1)/2` candidates leaves a number of choices tending to infinity, by the displayed assumption on j.

Each remaining n realizes the entire j-step prefix, all its states are actual positive integers, and those states are pairwise distinct.  The ballot condition makes them at least n.  This is exact prefix admission, not a probabilistic assertion about words.

### Even the optimal unordered tail bound still passes

Let k<=j be the number of odd states among the first j steps, and let F be their set of actual values.  Keep their exact correction product

    Q = product_(x in F) (1+1/(3*x)) >= 1.

To maximize the correction product over the remaining K-k distinct odd integers at least n and outside F, take the smallest available ones.  Call these `b_0<...<b_(K-k-1)`.  This is the sharpest bound that keeps the prefix and otherwise uses only unordered integer spacing.  Its upper product is

    M = Q * product_i (1+1/(3*b_i)).

There are only k excluded odd values, so `b_i<=n+2(k+i)`.  This inequality bounds M from BELOW, which is the right direction to show that its proposed upper bound is too large to exclude a candidate.  Expansion and the reciprocal-sum inequality give

    M >= 1 + (K-k)/(3*(n+K+k-1)).

The exact required correction from the whole word is still

    1+S/n <= 1+(7K+1)/(24*n).

For n>=10K and k=o(K), the first expression eventually exceeds the second.  Clearing denominators reduces the comparison to

    (K-1-8k)*n >= (7K+1)*(K+k-1).

Its left coefficient is eventually positive.  At the smallest allowed n=10K the difference between the two sides is

    3K^2 - 4K + 1 - 87Kk - k > 0

for all sufficiently large K, because k<=j=o(K).  Hence every remaining candidate passes the full mixed product inequality, not just its u-only weakening.

It also has a positive rational overshoot, since

    D*n/3^K = (u-1)*n <= 12K/100 < K/6 < S.

### The admitted prefix does not imply full admission

The candidate interval has length 2K, strictly smaller than 2^m.  Thus at most one of its integers realizes the WHOLE word v_K, while the construction leaves a number of prefix-admitted candidates tending to infinity.  In particular, many of them really are false candidates, irrespective of whether any genuine first-crossing survivor exists.

This proves the failure of exact-j-prefix admission plus the optimal unordered-tail-spacing relaxation at the stated scale `2^j*j^2=o(K)`.  It says nothing against order-sensitive tail constraints or substantially longer prefixes.  It is a precise obstruction to Fable's suggested repair, not an all-methods impossibility claim.

## 7. A monotonicity fact, with its scope kept narrow

Fable also observed that `f_K(n)=n*(P_K(n)-1)` increases with positive real n.  The claim is correct, but monotonicity of the first-order sum alone does not prove monotonicity of the product's higher-order terms.

A direct induction uses

    f_(K+1)(n) = f_K(n) + (n+f_K(n))/(3*(n+2K)),
    0 <= f_K(n) <= K/3.

The latter bound follows inductively from the same recurrence; it is strict for K>=2, while f_1=1/3.  The update is increasing in its f argument.  Holding f<=K/3 fixed, its derivative with respect to n is `(2K-f)/(3*(n+2K)^2)>=0`.  Thus f_K is nondecreasing, and strictly increasing for K>=2.  Expanding at infinity gives `f_K(n)->K/3` for fixed K.

Consequently the real solution set to the full spacing inequality `S<=f_K(n)` is a ray when nonempty.  This does not, by itself, prove every monotone necessary condition is incomplete: its intersection with an integer admission window might be empty or a single correct point.  Sections 3 and 6 give the needed concrete obstruction; section 6 supplies many integer candidates in an interval containing at most one full realizing residue.  No helper is justified merely to formalize this monotonicity observation.

## 8. Handoff

No candidate is endorsed for a proof lap.  The useful output is the precise scope correction and the explicit all-length failure of one positive-integer spacing relaxation.  Fable owns implementation and helper launches.  This note contains paper proofs and hand anchors, not claims of a new Lean theorem or of executed numerical tests.
