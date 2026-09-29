# Operator branch: arithmetic norm and coefficient tests, 2026-09-29

The exact anchored constant in `RESEARCH-2026-09-28-sharp-anchored-next.md` is `1/M_n` for a bounded nonperiodic strict future, and zero for an unbounded or periodic start.  `AnchoredCut.lean` proves the finite-cut lower bound; `OrbitPrefix.lean` proves the one-point defect identity.  Neither estimates `M_n` or excludes an orbit.  This pass asks whether a **change of coefficient class or defect norm** adds arithmetic without merely renaming the missing Collatz premise.  I found no credible new mechanism from these changes.

## Integrality and finite support do not change the sharp infimum

For a positive anchor `n≥3` and `L≥1`, write `q=T^L n`.  Truncate the dyadic ray at `H` and keep the same orbit prefix:

```
F_{L,H} = Σ_(h=0)^H δ_(2^h n) + Σ_(j=1)^(L−1) δ_(T^j n).
(P−I)F_{L,H} = δ_q − δ_(2^H n).                 (1)
```

This is a **finitely supported nonnegative integer** coefficient vector.  If `n` is nonperiodic, its strict future misses the ray, so `a_n=1`.  For the first maximum in the bounded case, the prefix also avoids `1,2`; for an unbounded orbit every prefix does.  In the original weighted norm its defect costs at most `1/q+1/(2^H n)`.  Letting `H→∞` gives the old upper bound `1/M_n` in the bounded case; choosing `q→∞` as well gives zero for an unbounded orbit.  The finite-cut lower bound still applies.  Thus requiring **integer coefficients, 0/1 coefficients, or finite support** does not repair the height degeneration.  Finite support can remove attainment but cannot raise the infimum.

More generally, if a proposed defect seminorm `N` obeys `N(b)≤C∑_{v≥1}|b_v|/v` on finitely supported `b`, then (1) gives `N((P−I)F_{L,H})≤C(1/q+1/(2^H n))`.  Every bounded postprocessing of the existing weighted defect space, including a bounded finite-stencil correlation operator, inherits the same zero-infimum construction on an unbounded orbit.  To change this input, a norm must be genuinely stronger or discontinuous relative to weighted ℓ¹.

## Stronger norms: what they detect and what they lose

The unweighted ℓ¹ norm is a sharp control.  On **finite-support** nonnegative coefficients with `a_n=1`, its defect infimum is `2` for every nonperiodic `n`, and `0` for periodic `n≥3`.  For the lower bound, let `A` be the whole strict future of a nonperiodic `n`.  It is forward closed and excludes `n`.  Although `A` may be infinite, the support of `b=(P−I)a` is finite, so the cut identity gives `Σ_(v∈A)b_v≥a_n=1`.  Finite-support mass conservation gives `Σ_v b_v=0`; hence `Σ_v|b_v|≥2`.  Equation (1) attains `2` because its endpoints are distinct.  A periodic start has the finite cycle indicator with zero defect.  This norm removes peak-height decay, but detects only whether the **anchor itself is periodic**; it gives the same value to a convergent transient start and a divergent one.  It does not resolve the hard divergence question.

A tempting non-diagonal addition is the global mass moment

```
N_mass(b)=Σ_v |b_v|/v + |Σ_v b_v|.
```

It charges a one-point defect `δ_q` by `1+1/q`.  But every finitely supported vector in (1) has total defect mass zero, so `N_mass((P−I)F_{L,H})=1/q+1/(2^H n)`.  The original infimum remains.  On the infinite ray-prefix vector the mass term jumps to one.  This is a boundary-at-infinity discontinuity, not a robust spectral estimate.

An arithmetic version can charge odd-prime incidence.  For a finite-support defect set

```
N_prime(b)=Σ_v |b_v|/v
           +Σ_(p odd prime) |Σ_(v:p|v)b_v|.
```

The second sum is finite on finite support.  Let `S(x)` be the set of odd prime divisors of `x`.  Equation (1) gives exactly

```
N_prime((P−I)F_{L,H})
  =1/q+1/(2^H n)+|S(q) △ S(n)|.                (2)
```

Even averaging many endpoint vectors does not dilute this particular charge: for `λ_i≥0`, `Σ_i λ_i=1`, the prime moment of `Σ_i λ_i δ_(q_i)−δ_(2^H n)` equals `Σ_i λ_i |S(q_i)△S(n)|`, because each coordinate difference from the 0/1 incidence vector of `n` has a fixed sign.  So (2) genuinely changes the cheap **prefix** construction when the endpoint changes prime support.

The difficult premise is now exposed rather than solved.  To recover the inference “divergence gives arbitrarily small defect,” one would need infinitely high future points with `S(q)=S(n)` or a different positive-vector construction whose prime moments cancel.  No such recurrence theorem or construction is present.  Even information about **adjacent** smooth orbit values would not control future visits separated by arbitrarily long trajectories.  Conversely, a lower bound in `N_prime` would be consistent with a divergent orbit, so it would not exclude divergence.  This is an arithmetic-sensitive norm but currently not a credible Collatz mechanism.

The exact operator implication remains clear in weighted ℓ¹ with exponent `s>1`.  If the orbit of `n` is unbounded, it has distinct positive states; hence `Σ_(j≥1)(T^j n)^(-s)≤ζ(s)`.  The infinite positive vector `D_n+Σ_(j≥1)δ_(T^j n)` belongs to that space, has `a_n=1`, avoids `1,2`, and has **exactly zero** defect coordinatewise.  A nontrivial periodic start also gives a finite exact fixed vector.  Showing that neither kind of nontrivial positive fixed vector exists would imply Collatz, but that exact uniqueness premise is the difficulty.  The tested norm changes supply no proof of it; a uniform gap in the original weighted norms is already defeated by the positive approximate vectors in `RESEARCH-2026-09-27-arithmetic-lifts-followup.md`.

## Finite congruence moments have no general cut

One might seek a bounded arithmetic dual certificate from a forward-closed set of residues modulo an odd `m`.  A residue `r` has both even and odd positive representatives, so the saturated quotient has both arrows

```
E(r)=r/2,       O(r)=(3r+1)/2    (mod m).
```

If `gcd(m,6)=1`, both are permutations.  Any forward-closed residue set is therefore invariant under them and their inverses.  The commutator `E O E⁻¹ O⁻¹` translates every residue by `−1/4` modulo `m`, a unit translation.  It acts transitively, so the only forward-closed residue sets are empty and all residues.  Such a finite congruence cut cannot separate `n` from its future.  Modulo three the proper closed set `{1,2}` merely detects the first exit from multiples of three; it already contains the hard-family anchors `cubicN(s)≡1 (mod 3)`.  Mixed moduli divisible by three are not excluded by this argument, but this pass found no separating certificate there.

**Decision (confidence 85%).**  The proved implications are the sharp cut/prefix constant, the finite-integer approximation (1), the unweighted ℓ¹ classification, and the saturated-residue obstruction above.  The unproved premise for an operator proof is qualitative exclusion of nontrivial positive exact fixed vectors (or an arithmetic dual certificate that separates every hard orbit while preserving the divergence implication).  No mechanism for that premise emerged from integrality, bounded correlations, global moments, prime incidence, or finite congruence cuts.  I would not launch a Lean theorem or a spectral computation on these modifications without a new mathematical certificate that survives (1) and still treats a hypothetical divergent orbit.
