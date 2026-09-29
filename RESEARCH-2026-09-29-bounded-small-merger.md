# No bounded-depth merger with any smaller seed on a CRT progression

Write \(T(x)=x/2\) for even integers and \(T(x)=(3x+1)/2\) for odd integers.  Use the same formula on negative integers only in the proof below.  For every \(K\ge0\), every positive integer \(n\) satisfying

\[
 n\ge6^K,\qquad 2^K\mid n+1,\qquad 3^K\mid n,
\]

and every \(0<b<n\), the two positive shortcut orbits do **not** meet with both depths at most \(K\):

\[
 T^i(n)\ne T^j(b)\qquad(0\le i,j\le K).
\]

The congruences have arbitrarily large positive solutions by CRT.  Thus for every finite depth there are infinitely many targets with no bounded-depth merger with **any** smaller positive seed, not merely with one named auxiliary.  This broadens the allowed-seed side of the repository's fixed-`q1` finite-depth separation theorem, while using a different target family in `RESEARCH-2026-09-29-q1-coalescence.md`; it does not concern mergers at unbounded depths or convergence.

## Proof

The first \(K\) steps of \(n\) are odd because \(n\equiv-1\pmod{2^K}\), and therefore

\[
 T^i(n)+1=(3/2)^i(n+1)\qquad(0\le i\le K).
\]

Every positive shortcut step satisfies \(T(x)+1\le(3/2)(x+1)\).  If \(b<n\) and \(j\le i\), then \(T^j(b)+1\le(3/2)^j(b+1)<(3/2)^i(n+1)=T^i(n)+1\).  Consequently a meeting requires \(j>i\).

Fix a candidate \(j>i\) and its actual length-\(j\) parity word \(w\) on \(b\).  Let \(p\) be its number of odd steps and \(r=j-p\) its number of even steps.  Its affine branch formula is

\[
 T^j(b)={3^p b+c_w\over2^j},\qquad
 g_w:=2^j+c_w.
\]

The constant \(g_w\) starts at 1; appending an odd step multiplies it by 3, while appending an even step at time \(t\) adds \(2^t\).  Induction gives

\[
 3^p\le g_w\le2^r3^p.
\]

Equating this branch with the all-odd branch on \(n\), and setting \(d=j-i\), yields

\[
 b=\alpha n+\gamma,\qquad
 \alpha=2^d3^{i-p},\qquad
 \gamma={2^d3^i-g_w\over3^p}>-2^r.
\]

If \(\alpha>1\), its denominator in lowest terms is at most \(3^K\), so \(\alpha-1\ge3^{-K}\).  Since \(n\ge6^K\), \((\alpha-1)n\ge2^K\ge2^r\), whence \(b>n\), a contradiction.  Equality \(\alpha=1\) is impossible for \(d>0\) because \(2^d=3^{p-i}\).  Hence the only case that could give \(b<n\) has \(\alpha<1\).

Put \(q=p-i>0\).  Since \(\alpha=2^d/3^q<1\) and \(3^K\mid n\), the equation for the integer \(b\) can be written

\[
 b=2^d(n/3^q)-L,
 \qquad L={g_w-2^d3^i\over3^p}\in\mathbb Z.
\]

The bound on \(g_w\), together with \(2^d3^i<3^p\), gives \(1\le L<2^r\).  In particular \(b\equiv-L\pmod{2^d}\).  The first \(d\) parity choices of \(b\) therefore agree with those of the **signed** integer \(-L\), since a length-\(d\) parity prefix depends only on the start modulo \(2^d\).  Let \(p_0\) count their odd steps and set \(z=T^d(-L)<0\).  Applying the shared affine branch to inputs separated by \(2^d(n/3^q)\) gives

\[
 y:=T^d(b)=3^{p_0-q}n+z.
\]

The remaining \(i\) steps of \(w\) have \(p-p_0\le i\) odd steps, hence \(p_0\ge q\).  Set \(a=p_0-q\ge0\).  Then \(y=3^a n+z\), and the remaining \(i\)-step word has exactly \(a\) even steps.  Define \(y_0=z-3^a<0\).  Because

\[
 y-y_0=3^a(n+1)\equiv0\pmod{2^i},
\]

\(y_0\) shares those remaining \(i\) parity choices with \(y\).  Their affine images differ by \(3^{i-a}3^a(n+1)/2^i=3^i(n+1)/2^i\).  The assumed meeting says \(T^i(y)=T^i(n)=3^i(n+1)/2^i-1\), so necessarily \(T^i(y_0)=-1\).

This is impossible.  A negative odd shortcut step never decreases absolute value, and a negative even step halves it.  Any signed path from \(y_0\) to \(-1\) with only \(a\) even steps must begin with \(|y_0|\le2^a\).  Yet \(z\le-1\) gives \(|y_0|=3^a-z\ge3^a+1>2^a\).  This contradiction disposes of every contracting-slope word and proves the theorem.

An equivalent algebraic final step may be easier to formalize.  Write the remaining \(i\)-word as \((3^{i-a}x+c)/2^i\).  The same constant bound gives \(c\le2^a3^{i-a}-2^i\).  Cancellation of the \(n\)-coefficients in the meeting equation gives \(3^{i-a}z+c=3^i-2^i\).  Since \(z\le-1\), the left side is at most \((2^a-1)3^{i-a}-2^i\), forcing \(3^a\le2^a-1\), again impossible.  This version does not need to construct the signed orbit \(y_0\); it only needs the negative prefix endpoint \(z\).

## Difficulty and formal target

The theorem shows that **bounded duration** of access to a smaller merged seed cannot cover all positive integers, even when the seed may be chosen adaptively from *every* \(b<n\).  [Monks' arithmetic-progression sufficiency theorem](https://monks.scranton.edu/files/pubs/SufficiencyRev4.pdf) is qualitative about eventual merging; this result is compatible with it.  It gives no bound on the depth at which merging can occur and no convergence proof.

A frozen Lean statement in the repository's shortcut notation would have the shape

```lean
theorem no_bounded_smaller_merger
    (K n : ℕ) (hn : 6 ^ K ≤ n)
    (h2 : 2 ^ K ∣ n + 1) (h3 : 3 ^ K ∣ n)
    (b : ℕ) (hb : 0 < b) (hbn : b < n)
    (i j : ℕ) (hi : i ≤ K) (hj : j ≤ K) :
    (FrontB.tstep^[i]) n ≠ (FrontB.tstep^[j]) b := by
  ...
```

This is a suggested statement, not a Lean proof.  The signed comparison can be isolated as a lemma about actual integer parity prefixes and the number of even steps in a negative path to \(-1\).  The repo's earlier negative inventory rules out treating finite word scans as a proof; the argument here covers all words symbolically.


## Scope and execution checkpoint

For K>0 these targets are divisible by3, whereas the current catalytic hard family has original targets congruent to1 modulo3.  Consequently this is a global obstruction to uniformly bounded smaller-seed certificates, not a proof that the uncovered catalytic progression itself has no bounded merger to any smaller seed.  It does not logically subsume the old Q1 theorem on that different progression.  No historical novelty is claimed.

The two actual-orbit statements are frozen in `CollatzMoonshot/Obstructions/BoundedMerger.lean`, with independent type consumers in `scripts/AxiomAudit.lean`.  A three-lap Opus/low run was launched as `collatz-moonshot-20260929-175724-902000`; see `KICKOFF-2026-09-29-bounded-merger.md`.  At this checkpoint the argument is a paper proof; Lean completion must be checked before reporting it as formalized.

The next positive premise would still be a mechanism giving unbounded-depth access to a smaller convergent seed, with a rank that controls its termination.  This obstruction establishes the necessity of allowing depth to grow, not a mechanism or a probability of success for such a rank.


## Persistent diagnostic

`experiments/repair_family.py bounded-merger K [--multiple M]` constructs a CRT witness and enumerates every positive inverse ancestor through depth K for every target prefix through depth K.  K is bounded to0..16; all arithmetic is exact.  The complete predecessor list of x is2x and, when x is2mod3, (2x−1)/3.  The instrument reports minima and depth coverage, and asserts the constructed witness has no smaller ancestor.  `--start N` instead diagnoses an arbitrary positive start and reports a smaller meeting if found; it does not assert the obstruction outside its hypotheses.

The persistent external suite is driven by `experiments/repair_family.py test`, which exercises the real CLI.  Hand controls include K1,n9 with aggregate ancestor counts[2,3], K2,n63 with counts[3,5,6], and the genuine merger from27 to31 in three steps.  These finite checks validate the instrument and examples, not the all-K theorem.


## Positive-only simplification used by the formalization

The signed-prefix comparison has an elementary natural-number replacement.  For positive integers x,C and any d, if `x<C*2^d`, then

```
T^d(x) < C*3^(number of odd steps in that prefix).
```

Prove this by induction on d.  At an even step halve the bound; at an odd step the integer inequality `x≤C*2^d−1` gives `T(x)<3*C*2^(d−1)`.  In the contracting-slope case above, `b<2^d*N` with `N=n/3^q` integral, so the intermediate vertex y satisfies `y<3^a*n` without introducing a signed map.  Its remaining i-step word has i−a odd steps.  The endpoint equality and upper bound on its tail constant give

```
3^(i-a)*y + g_tail = 3^i*n + 3^i,
g_tail ≤ 2^a*3^(i-a) ≤ 3^i.
```

Together these force `y≥3^a*n`, the contradiction.  The ternary divisibility is used to make N integral; the binary divisibility supplies the target's all-odd prefix.  This is a proof simplification of the same frozen theorem, not a new hypothesis.

The actual repository CLI suite passed all40 tests after the diagnostic was installed.  Lean validation is tracked separately; a passing finite diagnostic is not substituted for the general theorem.
